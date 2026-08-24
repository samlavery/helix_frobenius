import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 160` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT160 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((160 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))

theorem st160_c1 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((27911/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291557/2500000) (δ := 201/1000000000) (ψ := -466491/1000000) 160 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t1 : ((446551/500000 : ℚ) : ℝ) ≤ stT160 1 := by
  have hc : ((446551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446551/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((446551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c2 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-77933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4318251/10000000) (δ := 8131/1000000000) (ψ := -466491/1000000) 160 18
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t2 : ((-68905789893/625000000000 : ℚ) : ℝ) ≤ stT160 2 := by
  have hc : ((-38979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68905789893/625000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-38979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c3 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((190143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 197039/2500000) (δ := 8003/1000000000) (ψ := -466491/1000000) 160 28
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t3 : ((548866627883/1000000000000 : ℚ) : ℝ) ≤ stT160 3 := by
  have hc : ((190133/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548866627883/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((190133/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c4 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-711271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5905253/10000000) (δ := 161/20000000) (ψ := -466491/1000000) 160 35
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t4 : ((-3556605711321/10000000000000 : ℚ) : ℝ) ≤ stT160 4 := by
  have hc : ((-711321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3556605711321/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-711321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c5 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((933779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 457457/5000000) (δ := 2049/250000000) (ψ := -466491/1000000) 160 41
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t5 : ((835152428283/2000000000000 : ℚ) : ℝ) ≤ stT160 5 := by
  have hc : ((933729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((835152428283/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((933729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c6 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-302891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4696303/10000000) (δ := 8071/1000000000) (ψ := -466491/1000000) 160 46
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t6 : ((-1236751482503/10000000000000 : ℚ) : ℝ) ≤ stT160 6 := by
  have hc : ((-302941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1236751482503/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-302941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c7 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-700683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1466969/2500000) (δ := 8043/1000000000) (ψ := -466491/1000000) 160 50
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t7 : ((-529704395957/2000000000000 : ℚ) : ℝ) ≤ stT160 7 := by
  have hc : ((-700733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529704395957/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-700733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c8 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((246467/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210397/5000000) (δ := 8121/1000000000) (ψ := -466491/1000000) 160 53
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t8 : ((1742696035497/5000000000000 : ℚ) : ℝ) ≤ stT160 8 := by
  have hc : ((492909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1742696035497/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((492909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c9 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((39463/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51263/1250000) (δ := 8199/1000000000) (ψ := -466491/1000000) 160 56
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t9 : ((131536653513/400000000000 : ℚ) : ℝ) ≤ stT160 9 := by
  have hc : ((39461/40000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131536653513/400000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((39461/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c10 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-254217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -913917/2000000) (δ := 13/1600000) (ψ := -466491/1000000) 160 59
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t10 : ((-402031470113/5000000000000 : ℚ) : ℝ) ≤ stT160 10 := by
  have hc : ((-254267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402031470113/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-254267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c11 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((81987/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267321/1250000) (δ := 63/7812500) (ψ := -466491/1000000) 160 61
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t11 : ((988724900299/5000000000000 : ℚ) : ℝ) ≤ stT160 11 := by
  have hc : ((327923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((988724900299/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((327923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c12 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-597263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2763601/5000000) (δ := 4077/500000000) (ψ := -466491/1000000) 160 63
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t12 : ((-53884203043/312500000000 : ℚ) : ℝ) ≤ stT160 12 := by
  have hc : ((-597313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53884203043/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-597313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c13 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-385543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1225671/2000000) (δ := 1607/200000000) (ψ := -466491/1000000) 160 65
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t13 : ((-33417913549/156250000000 : ℚ) : ℝ) ≤ stT160 13 := by
  have hc : ((-12049/15625 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33417913549/156250000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-12049/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c14 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-21327/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4355629/10000000) (δ := 8183/1000000000) (ψ := -466491/1000000) 160 67
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t14 : ((-228062085129/5000000000000 : ℚ) : ℝ) ≤ stT160 14 := by
  have hc : ((-85333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228062085129/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-85333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c15 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((977031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268431/5000000) (δ := 4003/500000000) (ψ := -466491/1000000) 160 69
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t15 : ((630638304557/2500000000000 : ℚ) : ℝ) ≤ stT160 15 := by
  have hc : ((976981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630638304557/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((976981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c16 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-219583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1012733/2000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 71
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t16 : ((-68627527451/625000000000 : ℚ) : ℝ) ≤ stT160 16 := by
  have hc : ((-27451/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68627527451/625000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-27451/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c17 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((178549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 869553/2500000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 72
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t17 : ((108230905161/2500000000000 : ℚ) : ℝ) ≤ stT160 17 := by
  have hc : ((178499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108230905161/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((178499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c18 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-443003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2537177/5000000) (δ := 8133/1000000000) (ψ := -466491/1000000) 160 74
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t18 : ((-1044286111219/10000000000000 : ℚ) : ℝ) ≤ stT160 18 := by
  have hc : ((-443053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1044286111219/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-443053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c19 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((471739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 422281/5000000) (δ := 8163/1000000000) (ψ := -466491/1000000) 160 75
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t19 : ((541092987549/2500000000000 : ℚ) : ℝ) ≤ stT160 19 := by
  have hc : ((235857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541092987549/2500000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((235857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c20 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-159283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5653919/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 76
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t20 : ((-178097785047/1250000000000 : ℚ) : ℝ) ≤ stT160 20 := by
  have hc : ((-318591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178097785047/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-318591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c21 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-100021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6245927/10000000) (δ := 4081/500000000) (ψ := -466491/1000000) 160 78
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t21 : ((-873109457511/5000000000000 : ℚ) : ℝ) ≤ stT160 21 := by
  have hc : ((-400109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-873109457511/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-400109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c22 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((230353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3345891/10000000) (δ := 4067/500000000) (ψ := -466491/1000000) 160 79
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t22 : ((491007608121/10000000000000 : ℚ) : ℝ) ≤ stT160 22 := by
  have hc : ((230303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((491007608121/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((230303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c23 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((873109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636567/5000000) (δ := 8027/1000000000) (ψ := -466491/1000000) 160 80
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t23 : ((227556716937/1250000000000 : ℚ) : ℝ) ≤ stT160 23 := by
  have hc : ((873059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227556716937/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((873059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c24 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((499927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42743/10000000) (δ := 8083/1000000000) (ψ := -466491/1000000) 160 81
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t24 : ((510210229191/2500000000000 : ℚ) : ℝ) ≤ stT160 24 := by
  have hc : ((249951/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510210229191/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((249951/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c25 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((964979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33179/500000) (δ := 819/100000000) (ψ := -466491/1000000) 160 82
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t25 : ((964929/5000000 : ℚ) : ℝ) ≤ stT160 25 := by
  have hc : ((964929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((964929/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((964929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c26 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((193403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80487/1250000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 83
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t26 : ((379274809273/2000000000000 : ℚ) : ℝ) ≤ stT160 26 := by
  have hc : ((193393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379274809273/2000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((193393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c27 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((499959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32053/10000000) (δ := 1601/200000000) (ψ := -466491/1000000) 160 84
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t27 : ((962122983/5000000000 : ℚ) : ℝ) ≤ stT160 27 := by
  have hc : ((249967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((962122983/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((249967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c28 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((44989/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112883/1000000) (δ := 507/62500000) (ψ := -466491/1000000) 160 85
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t28 : ((85016477403/500000000000 : ℚ) : ℝ) ≤ stT160 28 := by
  have hc : ((89973/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85016477403/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((89973/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c29 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((6806/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1400137/5000000) (δ := 1023/125000000) (ψ := -466491/1000000) 160 86
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t29 : ((404383083951/5000000000000 : ℚ) : ℝ) ≤ stT160 29 := by
  have hc : ((217767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404383083951/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((217767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c30 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-99253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4947637/10000000) (δ := 8077/1000000000) (ψ := -466491/1000000) 160 87
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t30 : ((-181233192501/2500000000000 : ℚ) : ℝ) ≤ stT160 30 := by
  have hc : ((-198531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181233192501/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-198531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c31 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-496053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188491/250000) (δ := 8033/1000000000) (ψ := -466491/1000000) 160 88
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t31 : ((-222745719053/1250000000000 : ℚ) : ℝ) ≤ stT160 31 := by
  have hc : ((-248039/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222745719053/1250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-248039/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c32 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-236697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32249/62500) (δ := 8033/1000000000) (ψ := -466491/1000000) 160 88
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t32 : ((-209234669887/2500000000000 : ℚ) : ℝ) ≤ stT160 32 := by
  have hc : ((-118361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209234669887/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-118361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c33 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((6097/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1760517/10000000) (δ := 407/50000000) (ψ := -466491/1000000) 160 89
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t33 : ((6633009351/50000000000 : ℚ) : ℝ) ≤ stT160 33 := by
  have hc : ((30483/40000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6633009351/50000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((30483/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c34 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((10858/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2006247/10000000) (δ := 1631/200000000) (ψ := -466491/1000000) 160 90
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t34 : ((119167790707/1000000000000 : ℚ) : ℝ) ≤ stT160 34 := by
  have hc : ((347431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119167790707/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((347431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c35 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-48047/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -611921/1000000) (δ := 503/62500000) (ψ := -466491/1000000) 160 91
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t35 : ((-649756469909/5000000000000 : ℚ) : ℝ) ≤ stT160 35 := by
  have hc : ((-384401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-649756469909/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-384401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c36 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-469623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102983/200000) (δ := 503/62500000) (ψ := -466491/1000000) 160 91
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t36 : ((-782788489891/10000000000000 : ℚ) : ℝ) ≤ stT160 36 := by
  have hc : ((-469673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-782788489891/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-469673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c37 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((987177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400787/10000000) (δ := 4031/500000000) (ψ := -466491/1000000) 160 92
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t37 : ((1622825929603/10000000000000 : ℚ) : ℝ) ≤ stT160 37 := by
  have hc : ((987127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1622825929603/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((987127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c38 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-281313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579987/1250000) (δ := 8169/1000000000) (ψ := -466491/1000000) 160 93
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t38 : ((-91286255809/2000000000000 : ℚ) : ℝ) ≤ stT160 38 := by
  have hc : ((-281363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91286255809/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-281363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c39 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-666367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179697/312500) (δ := 8169/1000000000) (ψ := -466491/1000000) 160 93
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t39 : ((-533560773297/5000000000000 : ℚ) : ℝ) ≤ stT160 39 := by
  have hc : ((-666417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-533560773297/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-666417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c40 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((124713/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8473/500000) (δ := 8127/1000000000) (ψ := -466491/1000000) 160 94
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t40 : ((394357162563/2500000000000 : ℚ) : ℝ) ≤ stT160 40 := by
  have hc : ((498827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394357162563/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((498827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c41 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-127891/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5661463/10000000) (δ := 8019/1000000000) (ψ := -466491/1000000) 160 95
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t41 : ((-99873925969/1000000000000 : ℚ) : ℝ) ≤ stT160 41 := by
  have hc : ((-127901/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99873925969/1000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-127901/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c42 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-20233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3977577/10000000) (δ := 8019/1000000000) (ψ := -466491/1000000) 160 95
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t42 : ((-15648679311/5000000000000 : ℚ) : ℝ) ≤ stT160 42 := by
  have hc : ((-20283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15648679311/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-20283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c43 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((600017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1159093/5000000) (δ := 8091/1000000000) (ψ := -466491/1000000) 160 96
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t43 : ((182988135099/2000000000000 : ℚ) : ℝ) ≤ stT160 43 := by
  have hc : ((599967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182988135099/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((599967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c44 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-924701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3438807/5000000) (δ := 8091/1000000000) (ψ := -466491/1000000) 160 96
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t44 : ((-1394114843307/10000000000000 : ℚ) : ℝ) ≤ stT160 44 := by
  have hc : ((-924751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1394114843307/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-924751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c45 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((31187/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158771/10000000) (δ := 4099/500000000) (ψ := -466491/1000000) 160 97
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t45 : ((743815595537/5000000000000 : ℚ) : ℝ) ≤ stT160 45 := by
  have hc : ((498967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((743815595537/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((498967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c46 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-905373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6757633/10000000) (δ := 4049/500000000) (ψ := -466491/1000000) 160 98
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t46 : ((-66748688983/500000000000 : ℚ) : ℝ) ≤ stT160 46 := by
  have hc : ((-905423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66748688983/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-905423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c47 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((369923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1844887/10000000) (δ := 4049/500000000) (ψ := -466491/1000000) 160 98
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t47 : ((269775673901/2500000000000 : ℚ) : ℝ) ≤ stT160 47 := by
  have hc : ((184949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269775673901/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((184949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c48 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-284747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1360429/2500000) (δ := 2003/250000000) (ψ := -466491/1000000) 160 99
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t48 : ((-6422391723/78125000000 : ℚ) : ℝ) ≤ stT160 48 := by
  have hc : ((-71193/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6422391723/78125000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-71193/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c49 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((216767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701491/2500000) (δ := 2003/250000000) (ψ := -466491/1000000) 160 99
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t49 : ((154815667841/2500000000000 : ℚ) : ℝ) ≤ stT160 49 := by
  have hc : ((108371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154815667841/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((108371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c50 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-69997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4820879/10000000) (δ := 8119/1000000000) (ψ := -466491/1000000) 160 100
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t50 : ((-49502439749/1000000000000 : ℚ) : ℝ) ≤ stT160 50 := by
  have hc : ((-70007/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49502439749/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-70007/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c51 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((64947/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3100161/10000000) (δ := 8119/1000000000) (ψ := -466491/1000000) 160 100
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t51 : ((2273249559/50000000000 : ℚ) : ℝ) ≤ stT160 51 := by
  have hc : ((64937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2273249559/50000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((64937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c52 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-7147/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4840563/10000000) (δ := 511/62500000) (ψ := -466491/1000000) 160 101
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t52 : ((-2478124037/50000000000 : ℚ) : ℝ) ≤ stT160 52 := by
  have hc : ((-1787/5000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2478124037/50000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-1787/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c53 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((443329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2778717/10000000) (δ := 511/62500000) (ψ := -466491/1000000) 160 101
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t53 : ((121778050159/2000000000000 : ℚ) : ℝ) ≤ stT160 53 := by
  have hc : ((443279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121778050159/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((443279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c54 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-143251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2726203/5000000) (δ := 8069/1000000000) (ψ := -466491/1000000) 160 102
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t54 : ((-97478491089/1250000000000 : ℚ) : ℝ) ≤ stT160 54 := by
  have hc : ((-286527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97478491089/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-286527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c55 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((91043/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 943617/5000000) (δ := 8069/1000000000) (ψ := -466491/1000000) 160 102
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t55 : ((491015450653/5000000000000 : ℚ) : ℝ) ≤ stT160 55 := by
  have hc : ((364147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((491015450653/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((364147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c56 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-879369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6613329/10000000) (δ := 8041/1000000000) (ψ := -466491/1000000) 160 103
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t56 : ((-1175173765633/10000000000000 : ℚ) : ℝ) ≤ stT160 56 := by
  have hc : ((-879419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1175173765633/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-879419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c57 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((12283/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 466511/10000000) (δ := 8041/1000000000) (ψ := -466491/1000000) 160 103
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t57 : ((32536797447/250000000000 : ℚ) : ℝ) ≤ stT160 57 := by
  have hc : ((98259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32536797447/250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((98259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c58 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-985193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7423231/10000000) (δ := 8041/1000000000) (ψ := -466491/1000000) 160 103
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t58 : ((-258737619959/2000000000000 : ℚ) : ℝ) ≤ stT160 58 := by
  have hc : ((-985243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258737619959/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-985243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c59 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((418563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361743/2500000) (δ := 2037/250000000) (ψ := -466491/1000000) 160 104
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t59 : ((272445009141/2500000000000 : ℚ) : ℝ) ≤ stT160 59 := by
  have hc : ((209269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272445009141/2500000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((209269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c60 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-513751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1318967/2500000) (δ := 2037/250000000) (ψ := -466491/1000000) 160 104
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t60 : ((-132662904399/2000000000000 : ℚ) : ℝ) ≤ stT160 60 := by
  have hc : ((-513801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132662904399/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-513801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c61 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((42633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -477547/1250000) (δ := 2037/250000000) (ψ := -466491/1000000) 160 105
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t61 : ((3407619409/625000000000 : ℚ) : ℝ) ≤ stT160 61 := by
  have hc : ((42583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3407619409/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((42583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c62 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((19081/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167739/625000) (δ := 2037/250000000) (ψ := -466491/1000000) 160 105
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t62 : ((24230349079/400000000000 : ℚ) : ℝ) ≤ stT160 62 := by
  have hc : ((19079/40000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24230349079/400000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((19079/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c63 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-881389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6623979/10000000) (δ := 201/25000000) (ψ := -466491/1000000) 160 106
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t63 : ((-555254565099/5000000000000 : ℚ) : ℝ) ≤ stT160 63 := by
  have hc : ((-881439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-555254565099/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-881439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c64 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((49579/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324659/10000000) (δ := 201/25000000) (ψ := -466491/1000000) 160 106
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t64 : ((99153/800000 : ℚ) : ℝ) ≤ stT160 64 := by
  have hc : ((99153/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99153/800000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((99153/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c65 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-87911/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5877021/10000000) (δ := 201/25000000) (ψ := -466491/1000000) 160 106
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t65 : ((-109047985203/1250000000000 : ℚ) : ℝ) ≤ stT160 65 := by
  have hc : ((-351669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109047985203/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-351669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c66 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((8113/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1861971/5000000) (δ := 807/100000000) (ψ := -466491/1000000) 160 107
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t66 : ((1247531339/125000000000 : ℚ) : ℝ) ≤ stT160 66 := by
  have hc : ((2027/25000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1247531339/125000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((2027/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c67 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((608611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145609/5000000) (δ := 807/100000000) (ψ := -466491/1000000) 160 107
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t67 : ((371737661167/5000000000000 : ℚ) : ℝ) ≤ stT160 67 := by
  have hc : ((608561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371737661167/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((608561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c68 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-989461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1498141/2000000) (δ := 8177/1000000000) (ψ := -466491/1000000) 160 108
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t68 : ((-1199959209969/10000000000000 : ℚ) : ℝ) ≤ stT160 68 := by
  have hc : ((-989511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1199959209969/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-989511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c69 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((394851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330237/2000000) (δ := 8177/1000000000) (ψ := -466491/1000000) 160 108
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t69 : ((118828609677/1250000000000 : ℚ) : ℝ) ≤ stT160 69 := by
  have hc : ((197413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118828609677/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((197413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c70 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-35431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820859/2000000) (δ := 8177/1000000000) (ψ := -466491/1000000) 160 108
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t70 : ((-331078433/39062500000 : ℚ) : ℝ) ≤ stT160 70 := by
  have hc : ((-1108/15625 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331078433/39062500000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-1108/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c71 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-718147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5929829/10000000) (δ := 8119/1000000000) (ψ := -466491/1000000) 160 109
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t71 : ((-426171636027/5000000000000 : ℚ) : ℝ) ≤ stT160 71 := by
  have hc : ((-718197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426171636027/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-718197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c72 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((991019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335309/10000000) (δ := 8119/1000000000) (ψ := -466491/1000000) 160 109
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t72 : ((1167867867159/10000000000000 : ℚ) : ℝ) ≤ stT160 72 := by
  have hc : ((990969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1167867867159/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((990969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c73 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-481187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5182011/10000000) (δ := 8119/1000000000) (ψ := -466491/1000000) 160 109
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t73 : ((-140811389911/2500000000000 : ℚ) : ℝ) ≤ stT160 73 := by
  have hc : ((-481237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140811389911/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-481237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c74 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-111589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79433/156250) (δ := 2003/250000000) (ψ := -466491/1000000) 160 110
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t74 : ((-259468353831/5000000000000 : ℚ) : ℝ) ≤ stT160 74 := by
  have hc : ((-223203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259468353831/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-223203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c75 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((198697/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35691/1250000) (δ := 2003/250000000) (ψ := -466491/1000000) 160 110
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t75 : ((2294238789/20000000000 : ℚ) : ℝ) ≤ stT160 75 := by
  have hc : ((198687/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2294238789/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((198687/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c76 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-307603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697951/1250000) (δ := 2003/250000000) (ψ := -466491/1000000) 160 110
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t76 : ((-88218404653/1250000000000 : ℚ) : ℝ) ≤ stT160 76 := by
  have hc : ((-76907/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88218404653/1250000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-76907/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c77 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-377791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -979103/2000000) (δ := 4049/500000000) (ψ := -466491/1000000) 160 111
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t77 : ((-215294935323/5000000000000 : ℚ) : ℝ) ≤ stT160 77 := by
  have hc : ((-377841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215294935323/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-377841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c78 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((994351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53169/2000000) (δ := 4049/500000000) (ψ := -466491/1000000) 160 111
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t78 : ((1125824153377/10000000000000 : ℚ) : ℝ) ≤ stT160 78 := by
  have hc : ((994301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1125824153377/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((994301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c79 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-135703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1072289/2000000) (δ := 4049/500000000) (ψ := -466491/1000000) 160 111
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t79 : ((-9543242529/156250000000 : ℚ) : ℝ) ≤ stT160 79 := by
  have hc : ((-271431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9543242529/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-271431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c80 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-131779/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5314999/10000000) (δ := 8197/1000000000) (ψ := -466491/1000000) 160 112
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t80 : ((-147347377911/2500000000000 : ℚ) : ℝ) ≤ stT160 80 := by
  have hc : ((-263583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147347377911/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-263583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c81 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((495219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345999/10000000) (δ := 8197/1000000000) (ψ := -466491/1000000) 160 112
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t81 : ((275107750267/2500000000000 : ℚ) : ℝ) ≤ stT160 81 := by
  have hc : ((247597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275107750267/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((247597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c82 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-251297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4562041/10000000) (δ := 8197/1000000000) (ψ := -466491/1000000) 160 112
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t82 : ((-69391628413/2500000000000 : ℚ) : ℝ) ≤ stT160 82 := by
  have hc : ((-251347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69391628413/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-251347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c83 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-812337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3148681/5000000) (δ := 809/100000000) (ψ := -466491/1000000) 160 113
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t83 : ((-891710903841/10000000000000 : ℚ) : ℝ) ≤ stT160 83 := by
  have hc : ((-812387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-891710903841/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-812387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c84 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((411887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753451/5000000) (δ := 1609/100000000) (ψ := -466491/1000000) 160 113
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t84 : ((224689048859/2500000000000 : ℚ) : ℝ) ≤ stT160 84 := by
  have hc : ((205931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224689048859/2500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((205931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c85 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((276399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1613439/5000000) (δ := 809/100000000) (ψ := -466491/1000000) 160 113
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t85 : ((74935623887/2500000000000 : ℚ) : ℝ) ≤ stT160 85 := by
  have hc : ((276349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74935623887/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((276349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c86 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-99979/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1560537/2000000) (δ := 401/50000000) (ψ := -466491/1000000) 160 114
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t86 : ((-842308959/7812500000 : ℚ) : ℝ) ≤ stT160 86 := by
  have hc : ((-6249/6250 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-842308959/7812500000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-6249/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c87 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((29501/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -127133/400000) (δ := 401/50000000) (ψ := -466491/1000000) 160 114
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t87 : ((247054809/7812500000 : ℚ) : ℝ) ≤ stT160 87 := by
  have hc : ((3687/12500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247054809/7812500000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((3687/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c88 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((424353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278631/2000000) (δ := 401/50000000) (ψ := -466491/1000000) 160 114
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t88 : ((56541865123/625000000000 : ℚ) : ℝ) ≤ stT160 88 := by
  have hc : ((53041/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56541865123/625000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((53041/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c89 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-713433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1182591/2000000) (δ := 401/50000000) (ψ := -466491/1000000) 160 114
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t89 : ((-378145276517/5000000000000 : ℚ) : ℝ) ≤ stT160 89 := by
  have hc : ((-713483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378145276517/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-713483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c90 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-106149/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665711/1250000) (δ := 8127/1000000000) (ψ := -466491/1000000) 160 115
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t90 : ((-111901458787/2000000000000 : ℚ) : ℝ) ≤ stT160 90 := by
  have hc : ((-106159/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111901458787/2000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-106159/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c91 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((233771/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226437/2500000) (δ := 16127/1000000000) (ψ := -466491/1000000) 160 115
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t91 : ((122522647707/1250000000000 : ℚ) : ℝ) ≤ stT160 91 := by
  have hc : ((467517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122522647707/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((467517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c92 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((183403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 216617/625000) (δ := 8127/1000000000) (ψ := -466491/1000000) 160 115
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t92 : ((47789675979/2500000000000 : ℚ) : ℝ) ≤ stT160 92 := by
  have hc : ((183353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47789675979/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((183353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c93 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-39987/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 973779/1250000) (δ := 8127/1000000000) (ψ := -466491/1000000) 160 115
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t93 : ((-5183334191/50000000000 : ℚ) : ℝ) ≤ stT160 93 := by
  have hc : ((-39989/40000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5183334191/50000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-39989/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c94 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((114699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -909903/2500000) (δ := 8169/1000000000) (ψ := -466491/1000000) 160 116
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t94 : ((118251386229/10000000000000 : ℚ) : ℝ) ≤ stT160 94 := by
  have hc : ((114649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118251386229/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((114649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c95 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((485989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148307/2500000) (δ := 8169/1000000000) (ψ := -466491/1000000) 160 116
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t95 : ((62323546599/625000000000 : ℚ) : ℝ) ≤ stT160 95 := by
  have hc : ((121491/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62323546599/625000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((121491/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c96 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-4191/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195437/2500000) (δ := 8169/1000000000) (ψ := -466491/1000000) 160 116
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t96 : ((-34224483993/1000000000000 : ℚ) : ℝ) ≤ stT160 96 := by
  have hc : ((-33533/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34224483993/1000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-33533/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c97 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-454659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1356219/2000000) (δ := 8061/1000000000) (ψ := -466491/1000000) 160 117
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t97 : ((-115415508837/1250000000000 : ℚ) : ℝ) ≤ stT160 97 := by
  have hc : ((-113671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115415508837/1250000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-113671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c98 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((478897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -535699/2000000) (δ := 8061/1000000000) (ψ := -466491/1000000) 160 117
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t98 : ((60463531843/1250000000000 : ℚ) : ℝ) ≤ stT160 98 := by
  have hc : ((478847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60463531843/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((478847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c99 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((10637/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276493/2000000) (δ := 8061/1000000000) (ψ := -466491/1000000) 160 117
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t99 : ((85519603367/1000000000000 : ℚ) : ℝ) ≤ stT160 99 := by
  have hc : ((85091/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85519603367/1000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((85091/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c100 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-278279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1080517/2000000) (δ := 8061/1000000000) (ψ := -466491/1000000) 160 117
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t100 : ((-8697/156250 : ℚ) : ℝ) ≤ stT160 100 := by
  have hc : ((-8697/15625 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8697/156250 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-8697/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c101 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-163757/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3162609/5000000) (δ := 8049/1000000000) (ψ := -466491/1000000) 160 118
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t101 : ((-81477194073/1000000000000 : ℚ) : ℝ) ≤ stT160 101 := by
  have hc : ((-163767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81477194073/1000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-163767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c102 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((289327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1192149/5000000) (δ := 8049/1000000000) (ψ := -466491/1000000) 160 118
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t102 : ((143225753697/2500000000000 : ℚ) : ℝ) ≤ stT160 102 := by
  have hc : ((144651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143225753697/2500000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((144651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c103 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((25663/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759071/5000000) (δ := 8049/1000000000) (ψ := -466491/1000000) 160 118
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t103 : ((404559336807/5000000000000 : ℚ) : ℝ) ≤ stT160 103 := by
  have hc : ((410583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404559336807/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((410583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c104 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-11/20 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2691451/5000000) (δ := 8049/1000000000) (ψ := -466491/1000000) 160 118
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t104 : ((-10787371581/200000000000 : ℚ) : ℝ) ≤ stT160 104 := by
  have hc : ((-11001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10787371581/200000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-11001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c105 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-856323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6497261/10000000) (δ := 2039/250000000) (ψ := -466491/1000000) 160 119
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t105 : ((-835735267073/10000000000000 : ℚ) : ℝ) ≤ stT160 105 := by
  have hc : ((-856373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-835735267073/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-856373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c106 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((58661/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2705781/10000000) (δ := 2039/250000000) (ψ := -466491/1000000) 160 119
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t106 : ((45576383083/1000000000000 : ℚ) : ℝ) ≤ stT160 106 := by
  have hc : ((234619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45576383083/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((234619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c107 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((456533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1050139/10000000) (δ := 2039/250000000) (ψ := -466491/1000000) 160 119
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t107 : ((6895667467/78125000000 : ℚ) : ℝ) ≤ stT160 107 := by
  have hc : ((114127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6895667467/78125000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((114127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c108 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-5176/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4771099/10000000) (δ := 2039/250000000) (ψ := -466491/1000000) 160 119
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t108 : ((-159403613907/5000000000000 : ℚ) : ℝ) ≤ stT160 108 := by
  have hc : ((-165657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159403613907/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-165657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c109 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-48549/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290009/400000) (δ := 407/50000000) (ψ := -466491/1000000) 160 120
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t109 : ((-93007875181/1000000000000 : ℚ) : ℝ) ≤ stT160 109 := by
  have hc : ((-97103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93007875181/1000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-97103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c110 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((32881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143889/400000) (δ := 407/50000000) (ψ := -466491/1000000) 160 120
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t110 : ((31338865747/2500000000000 : ℚ) : ℝ) ≤ stT160 110 := by
  have hc : ((65737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31338865747/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((65737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c111 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((999959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4547/2000000) (δ := 407/50000000) (ψ := -466491/1000000) 160 120
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t111 : ((949070626713/10000000000000 : ℚ) : ℝ) ≤ stT160 111 := by
  have hc : ((999909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949070626713/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((999909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c112 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((126387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144407/400000) (δ := 407/50000000) (ψ := -466491/1000000) 160 120
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t112 : ((119377221007/10000000000000 : ℚ) : ℝ) ≤ stT160 112 := by
  have hc : ((126337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119377221007/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((126337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c113 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-240587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286631/400000) (δ := 407/50000000) (ψ := -466491/1000000) 160 120
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t113 : ((-452674004479/5000000000000 : ℚ) : ℝ) ≤ stT160 113 := by
  have hc : ((-481199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452674004479/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-481199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c114 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-52833/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1254487/2500000) (δ := 8033/1000000000) (ψ := -466491/1000000) 160 121
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t114 : ((-98977003601/2500000000000 : ℚ) : ℝ) ≤ stT160 114 := by
  have hc : ((-211357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98977003601/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-211357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c115 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((81977/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381117/2500000) (δ := 8033/1000000000) (ψ := -466491/1000000) 160 121
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t115 : ((2388725559/31250000000 : ℚ) : ℝ) ≤ stT160 115 := by
  have hc : ((20493/25000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2388725559/31250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((20493/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c116 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((178519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484683/2500000) (δ := 8033/1000000000) (ψ := -466491/1000000) 160 121
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t116 : ((82869500547/1250000000000 : ℚ) : ℝ) ≤ stT160 116 := by
  have hc : ((357013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82869500547/1250000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((357013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c117 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-546437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1343063/2500000) (δ := 8033/1000000000) (ψ := -466491/1000000) 160 121
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t117 : ((-505227777987/10000000000000 : ℚ) : ℝ) ≤ stT160 117 := by
  have hc : ((-546487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505227777987/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-546487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c118 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-932681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6931431/10000000) (δ := 8077/1000000000) (ψ := -466491/1000000) 160 122
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t118 : ((-34345953613/400000000000 : ℚ) : ℝ) ≤ stT160 118 := by
  have hc : ((-932731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34345953613/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-932731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c119 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((147887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3555911/10000000) (δ := 8077/1000000000) (ψ := -466491/1000000) 160 122
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t119 : ((67760941113/5000000000000 : ℚ) : ℝ) ≤ stT160 119 := by
  have hc : ((147837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67760941113/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((147837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c120 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((996521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208591/10000000) (δ := 8077/1000000000) (ψ := -466491/1000000) 160 122
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t120 : ((90964848177/1000000000000 : ℚ) : ℝ) ≤ stT160 120 := by
  have hc : ((996471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90964848177/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((996471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c121 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((320659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3110929/10000000) (δ := 8077/1000000000) (ψ := -466491/1000000) 160 122
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t121 : ((29146243581/1000000000000 : ℚ) : ℝ) ≤ stT160 121 := by
  have hc : ((320609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29146243581/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((320609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c122 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-209069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6403129/10000000) (δ := 8077/1000000000) (ψ := -466491/1000000) 160 122
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t122 : ((-189293608677/2500000000000 : ℚ) : ℝ) ≤ stT160 122 := by
  have hc : ((-418163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189293608677/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-418163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c123 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-747977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3019757/5000000) (δ := 1637/200000000) (ψ := -466491/1000000) 160 123
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t123 : ((-67447350509/1000000000000 : ℚ) : ℝ) ≤ stT160 123 := by
  have hc : ((-748027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67447350509/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-748027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c124 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((217727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1400317/5000000) (δ := 1637/200000000) (ψ := -466491/1000000) 160 123
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t124 : ((48875514063/1250000000000 : ℚ) : ℝ) ≤ stT160 124 := by
  have hc : ((108851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48875514063/1250000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((108851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c125 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((197287/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 206123/5000000) (δ := 1637/200000000) (ψ := -466491/1000000) 160 123
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t125 : ((176449875279/2000000000000 : ℚ) : ℝ) ≤ stT160 125 := by
  have hc : ((197277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176449875279/2000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((197277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c126 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((32653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1799763/5000000) (δ := 1637/200000000) (ψ := -466491/1000000) 160 123
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t126 : ((5815688447/500000000000 : ℚ) : ℝ) ≤ stT160 126 := by
  have hc : ((65281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5815688447/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((65281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c127 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-22651/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3380783/5000000) (δ := 1637/200000000) (ψ := -466491/1000000) 160 123
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t127 : ((-80402530413/1000000000000 : ℚ) : ℝ) ≤ stT160 127 := by
  have hc : ((-90609/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80402530413/1000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-90609/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c128 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-341861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2904559/5000000) (δ := 8111/1000000000) (ψ := -466491/1000000) 160 124
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t128 : ((-37773445653/625000000000 : ℚ) : ℝ) ≤ stT160 128 := by
  have hc : ((-170943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37773445653/625000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-170943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c129 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((94531/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348119/5000000) (δ := 8111/1000000000) (ψ := -466491/1000000) 160 124
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t129 : ((1664420289/40000000000 : ℚ) : ℝ) ≤ stT160 129 := by
  have hc : ((94521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1664420289/40000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((94521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c130 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((987697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196281/5000000) (δ := 8111/1000000000) (ψ := -466491/1000000) 160 124
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t130 : ((433111851263/5000000000000 : ℚ) : ℝ) ≤ stT160 130 := by
  have hc : ((987647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433111851263/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((987647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c131 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((186607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1728861/5000000) (δ := 8111/1000000000) (ψ := -466491/1000000) 160 124
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t131 : ((20374449641/1250000000000 : ℚ) : ℝ) ≤ stT160 131 := by
  have hc : ((186557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20374449641/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((186557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c132 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-428399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3249781/5000000) (δ := 8111/1000000000) (ψ := -466491/1000000) 160 124
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t132 : ((-46611942117/625000000000 : ℚ) : ℝ) ≤ stT160 132 := by
  have hc : ((-53553/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46611942117/625000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-53553/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c133 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-786433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6189521/10000000) (δ := 2001/250000000) (ψ := -466491/1000000) 160 125
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t133 : ((-68196727413/1000000000000 : ℚ) : ℝ) ≤ stT160 133 := by
  have hc : ((-786483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68196727413/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-786483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c134 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((289297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3193261/10000000) (δ := 4001/250000000) (ψ := -466491/1000000) 160 125
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t134 : ((62467806849/2500000000000 : ℚ) : ℝ) ≤ stT160 134 := by
  have hc : ((289247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62467806849/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((289247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c135 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((249039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219281/10000000) (δ := 2001/250000000) (ψ := -466491/1000000) 160 125
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t135 : ((214327645543/2500000000000 : ℚ) : ℝ) ≤ stT160 135 := by
  have hc : ((498053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214327645543/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((498053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c136 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((459731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2732759/10000000) (δ := 2001/250000000) (ψ := -466491/1000000) 160 125
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t136 : ((98543195013/2500000000000 : ℚ) : ℝ) ≤ stT160 136 := by
  have hc : ((459681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98543195013/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((459681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c137 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-159997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5663199/10000000) (δ := 2001/250000000) (ψ := -466491/1000000) 160 125
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t137 : ((-136705396401/2500000000000 : ℚ) : ℝ) ≤ stT160 137 := by
  have hc : ((-320019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136705396401/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-320019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c138 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-959007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1783921/2500000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 126
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t138 : ((-816403984649/10000000000000 : ℚ) : ℝ) ≤ stT160 138 := by
  have hc : ((-959057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-816403984649/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-959057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c139 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-63939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1061891/2500000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 126
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t139 : ((-13563390299/1250000000000 : ℚ) : ℝ) ≤ stT160 139 := by
  have hc : ((-15991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13563390299/1250000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-15991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c140 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((851443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345041/2500000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 126
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t140 : ((359779099761/5000000000000 : ℚ) : ℝ) ≤ stT160 140 := by
  have hc : ((851393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359779099761/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((851393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c141 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((416381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 366699/2500000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 126
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t141 : ((87658655439/1250000000000 : ℚ) : ℝ) ≤ stT160 141 := by
  have hc : ((104089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87658655439/1250000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((104089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c142 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-146149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1073419/2500000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 126
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t142 : ((-61343784609/5000000000000 : ℚ) : ℝ) ≤ stT160 142 := by
  have hc : ((-146199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61343784609/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-146199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c143 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-19099/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1775179/2500000) (δ := 4053/500000000) (ψ := -466491/1000000) 160 126
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t143 : ((-159722413/2000000000 : ℚ) : ℝ) ≤ stT160 143 := by
  have hc : ((-191/200 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159722413/2000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-191/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c144 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-171709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181869/312500) (δ := 819/100000000) (ψ := -466491/1000000) 160 127
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t144 : ((-143101364481/2500000000000 : ℚ) : ℝ) ≤ stT160 144 := by
  have hc : ((-343443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143101364481/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-343443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c145 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((171521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381451/1250000) (δ := 819/100000000) (ψ := -466491/1000000) 160 127
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t145 : ((8901221199/312500000000 : ℚ) : ℝ) ≤ stT160 145 := by
  have hc : ((21437/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8901221199/312500000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((21437/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c146 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((992691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18903/625000) (δ := 819/100000000) (ψ := -466491/1000000) 160 127
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t146 : ((164302930961/2000000000000 : ℚ) : ℝ) ≤ stT160 146 := by
  have hc : ((992641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164302930961/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((992641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c147 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((282169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303489/1250000) (δ := 819/100000000) (ψ := -466491/1000000) 160 127
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t147 : ((3636069081/78125000000 : ℚ) : ℝ) ≤ stT160 147 := by
  have hc : ((8817/15625 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3636069081/78125000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((8817/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c148 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-93263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321237/625000) (δ := 819/100000000) (ψ := -466491/1000000) 160 127
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t148 : ((-15333987927/400000000000 : ℚ) : ℝ) ≤ stT160 148 := by
  have hc : ((-93273/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15333987927/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-93273/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c149 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-499983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979179/1250000) (δ := 819/100000000) (ψ := -466491/1000000) 160 127
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t149 : ((-1600088101/19531250000 : ℚ) : ℝ) ≤ stT160 149 := by
  have hc : ((-62501/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1600088101/19531250000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-62501/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c150 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-487123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5198971/10000000) (δ := 8083/1000000000) (ψ := -466491/1000000) 160 128
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t150 : ((-397775292981/10000000000000 : ℚ) : ℝ) ≤ stT160 150 := by
  have hc : ((-487173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397775292981/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-487173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c151 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((263193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2541131/10000000) (δ := 8083/1000000000) (ψ := -466491/1000000) 160 128
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t151 : ((52285879/1220703125 : ℚ) : ℝ) ≤ stT160 151 := by
  have hc : ((8224/15625 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52285879/1220703125 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((8224/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c152 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((499607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99149/10000000) (δ := 8083/1000000000) (ψ := -466491/1000000) 160 128
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t152 : ((202607228637/2500000000000 : ℚ) : ℝ) ≤ stT160 152 := by
  have hc : ((249791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202607228637/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((249791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c153 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((46351/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2722109/10000000) (δ := 8083/1000000000) (ψ := -466491/1000000) 160 128
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t153 : ((4683564549/125000000000 : ℚ) : ℝ) ≤ stT160 153 := by
  have hc : ((23173/50000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4683564549/125000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((23173/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c154 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-132881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5327989/10000000) (δ := 8083/1000000000) (ψ := -466491/1000000) 160 128
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t154 : ((-214177277701/5000000000000 : ℚ) : ℝ) ≤ stT160 154 := by
  have hc : ((-265787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214177277701/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-265787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c155 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-499841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3895487/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t155 : ((-10037559213/125000000000 : ℚ) : ℝ) ≤ stT160 155 := by
  have hc : ((-249933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10037559213/125000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-249933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c156 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-49397/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2609307/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t156 : ((-19776633341/500000000000 : ℚ) : ℝ) ≤ stT160 156 := by
  have hc : ((-24701/50000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19776633341/500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-24701/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c157 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((121109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331347/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t157 : ((96645421299/2500000000000 : ℚ) : ℝ) ≤ stT160 157 := by
  have hc : ((242193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96645421299/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((242193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c158 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((99879/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61507/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t158 : ((39727729909/500000000000 : ℚ) : ℝ) ≤ stT160 158 := by
  have hc : ((49937/50000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39727729909/500000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((49937/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c159 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((286651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1200333/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t159 : ((113654517963/2500000000000 : ℚ) : ℝ) ≤ stT160 159 := by
  have hc : ((143313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113654517963/2500000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((143313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c160 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-191299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2454253/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t160 : ((-3781375367/125000000000 : ℚ) : ℝ) ≤ stT160 160 := by
  have hc : ((-47831/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3781375367/125000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-47831/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c161 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-122951/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3700353/5000000) (δ := 2007/250000000) (ψ := -466491/1000000) 160 129
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t161 : ((-387615845019/5000000000000 : ℚ) : ℝ) ≤ stT160 161 := by
  have hc : ((-491829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387615845019/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-491829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c162 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-344963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5830457/10000000) (δ := 1627/200000000) (ψ := -466491/1000000) 160 130
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t162 : ((-2710484469/50000000000 : ℚ) : ℝ) ≤ stT160 162 := by
  have hc : ((-86247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2710484469/50000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-86247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c163 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((55347/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3368897/10000000) (δ := 1627/200000000) (ψ := -466491/1000000) 160 130
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t163 : ((4334130047/250000000000 : ℚ) : ℝ) ≤ stT160 163 := by
  have hc : ((110669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4334130047/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((110669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c164 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((9327/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922417/10000000) (δ := 1627/200000000) (ψ := -466491/1000000) 160 130
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t164 : ((3641382701/50000000000 : ℚ) : ℝ) ≤ stT160 164 := by
  have hc : ((18653/20000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3641382701/50000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((18653/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c165 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((102907/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1509183/10000000) (δ := 1627/200000000) (ψ := -466491/1000000) 160 130
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t165 : ((160216056147/2500000000000 : ℚ) : ℝ) ≤ stT160 165 := by
  have hc : ((411603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160216056147/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((411603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c166 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((71/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3926103/10000000) (δ := 1627/200000000) (ψ := -466491/1000000) 160 130
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t166 : ((946903/40000000000 : ℚ) : ℝ) ≤ stT160 166 := by
  have hc : ((61/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((946903/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((61/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c167 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-819547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6328543/10000000) (δ := 1627/200000000) (ψ := -466491/1000000) 160 130
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t167 : ((-9909747327/156250000000 : ℚ) : ℝ) ≤ stT160 167 := by
  have hc : ((-819597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9909747327/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-819597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c168 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-470531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6991381/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t168 : ((-90760488363/1250000000000 : ℚ) : ℝ) ≤ stT160 168 := by
  have hc : ((-117639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90760488363/1250000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-117639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c169 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-27269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4617461/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t169 : ((-10490003147/500000000000 : ℚ) : ℝ) ≤ stT160 169 := by
  have hc : ((-13637/50000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10490003147/500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-13637/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c170 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((19351/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2257581/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t170 : ((59361287931/1250000000000 : ℚ) : ℝ) ≤ stT160 170 := by
  have hc : ((309591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59361287931/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((309591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c171 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((499687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88459/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t171 : ((191050512489/2500000000000 : ℚ) : ℝ) ≤ stT160 171 := by
  have hc : ((249831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191050512489/2500000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((249831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c172 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((283339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2420819/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t172 : ((27003082311/625000000000 : ℚ) : ℝ) ≤ stT160 172 := by
  have hc : ((141657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27003082311/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((141657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c173 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-319373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4739659/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t173 : ((-121426417489/5000000000000 : ℚ) : ℝ) ≤ stT160 173 := by
  have hc : ((-319423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121426417489/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-319423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c174 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-948117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7045139/10000000) (δ := 8161/1000000000) (ψ := -466491/1000000) 160 131
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t174 : ((-718804454533/10000000000000 : ℚ) : ℝ) ≤ stT160 174 := by
  have hc : ((-948167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-718804454533/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-948167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c175 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-414529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398159/625000) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t175 : ((-156686695333/2500000000000 : ℚ) : ℝ) ≤ stT160 175 := by
  have hc : ((-207277/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156686695333/2500000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-207277/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c176 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-32847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -255709/625000) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t176 : ((-3097277911/625000000000 : ℚ) : ℝ) ≤ stT160 176 := by
  have hc : ((-4109/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3097277911/625000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-4109/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c177 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((46573/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14258/78125) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t177 : ((140016241057/2500000000000 : ℚ) : ℝ) ≤ stT160 177 := by
  have hc : ((372559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140016241057/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((372559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c178 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((985347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26781/625000) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t178 : ((738510645707/10000000000000 : ℚ) : ℝ) ≤ stT160 178 := by
  have hc : ((985297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((738510645707/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((985297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c179 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((241041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 333677/1250000) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t179 : ((4503594849/125000000000 : ℚ) : ℝ) ≤ stT160 179 := by
  have hc : ((30127/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4503594849/125000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((30127/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c180 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-378643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612227/1250000) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t180 : ((-70565274927/2500000000000 : ℚ) : ℝ) ≤ stT160 180 := by
  have hc : ((-378693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70565274927/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-378693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c181 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-956501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889237/1250000) (δ := 4027/500000000) (ψ := -466491/1000000) 160 132
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t181 : ((-142199915109/2000000000000 : ℚ) : ℝ) ≤ stT160 181 := by
  have hc : ((-956551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142199915109/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-956551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c182 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-166687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6390227/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t182 : ((-98851321/1600000000 : ℚ) : ℝ) ≤ stT160 182 := by
  have hc : ((-166697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98851321/1600000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-166697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c183 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-108361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4198427/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t183 : ((-40069898121/5000000000000 : ℚ) : ℝ) ≤ stT160 183 := by
  have hc : ((-108411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40069898121/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-108411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c184 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((345677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2018587/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t184 : ((63704441317/1250000000000 : ℚ) : ℝ) ≤ stT160 184 := by
  have hc : ((86413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63704441317/1250000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((86413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c185 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((499107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149453/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t185 : ((91733018387/1250000000000 : ℚ) : ℝ) ≤ stT160 185 := by
  have hc : ((249541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91733018387/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((249541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c186 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((603981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2305773/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t186 : ((88564669357/2000000000000 : ℚ) : ℝ) ≤ stT160 186 := by
  have hc : ((603931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88564669357/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((603931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c187 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-41581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4450573/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t187 : ((-30414375343/2000000000000 : ℚ) : ℝ) ≤ stT160 187 := by
  have hc : ((-41591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30414375343/2000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-41591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c188 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-436851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6583893/10000000) (δ := 1007/125000000) (ψ := -466491/1000000) 160 133
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t188 : ((-3186245887/50000000000 : ℚ) : ℝ) ≤ stT160 188 := by
  have hc : ((-109219/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3186245887/50000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-109219/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c189 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-471247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -700203/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t189 : ((-42849994237/625000000000 : ℚ) : ℝ) ≤ stT160 189 := by
  have hc : ((-58909/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42849994237/625000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-58909/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c190 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-94051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489123/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t190 : ((-136481811579/5000000000000 : ℚ) : ℝ) ≤ stT160 190 := by
  have hc : ((-188127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136481811579/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-188127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c191 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((438751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279147/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t191 : ((158716318687/5000000000000 : ℚ) : ℝ) ≤ stT160 191 := by
  have hc : ((438701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158716318687/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((438701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c192 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((192151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70271/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t192 : ((138665661867/2000000000000 : ℚ) : ℝ) ≤ stT160 192 := by
  have hc : ((192141/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138665661867/2000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((192141/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c193 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((852481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137521/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t193 : ((122718524053/2000000000000 : ℚ) : ℝ) ≤ stT160 193 := by
  have hc : ((852431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122718524053/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((852431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c194 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((192621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344241/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t194 : ((69128945009/5000000000000 : ℚ) : ℝ) ≤ stT160 194 := by
  have hc : ((192571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69128945009/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((192571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c195 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-73521/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549897/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t195 : ((-42123173307/1000000000000 : ℚ) : ℝ) ≤ stT160 195 := by
  have hc : ((-294109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42123173307/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-294109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c196 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-992373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 754501/1000000) (δ := 2041/250000000) (ψ := -466491/1000000) 160 134
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t196 : ((-354436927489/5000000000000 : ℚ) : ℝ) ≤ stT160 196 := by
  have hc : ((-992423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354436927489/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-992423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c197 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-770821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3063657/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t197 : ((-549223232241/10000000000000 : ℚ) : ℝ) ≤ stT160 197 := by
  have hc : ((-770871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549223232241/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-770871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c198 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-8743/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2050997/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t198 : ((-2487131799/500000000000 : ℚ) : ℝ) ≤ stT160 198 := by
  have hc : ((-34997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2487131799/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-34997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c199 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((671363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1043437/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t199 : ((475881030753/10000000000000 : ℚ) : ℝ) ≤ stT160 199 := by
  have hc : ((671313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475881030753/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((671313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c200 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((124933/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40937/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t200 : ((176672908971/2500000000000 : ℚ) : ℝ) ≤ stT160 200 := by
  have hc : ((499707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176672908971/2500000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((499707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c201 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((360599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 956583/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t201 : ((25432906803/500000000000 : ℚ) : ℝ) ≤ stT160 201 := by
  have hc : ((180287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25432906803/500000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((180287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c202 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((5749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1949123/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t202 : ((1006847307/1250000000000 : ℚ) : ℝ) ≤ stT160 202 := by
  have hc : ((1431/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1006847307/1250000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((1431/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c203 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-140461/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2936783/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t203 : ((-98591397473/2000000000000 : ℚ) : ℝ) ≤ stT160 203 := by
  have hc : ((-140471/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98591397473/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-140471/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c204 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-499991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3919583/5000000) (δ := 2033/250000000) (ψ := -466491/1000000) 160 135
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t204 : ((-21880106391/312500000000 : ℚ) : ℝ) ≤ stT160 204 := by
  have hc : ((-31251/31250 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21880106391/312500000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-31251/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c205 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-713389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5912797/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t205 : ((-498287914209/10000000000000 : ℚ) : ℝ) ≤ stT160 205 := by
  have hc : ((-713439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498287914209/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-713439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c206 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-1573/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3966317/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t206 : ((-274861563/250000000000 : ℚ) : ℝ) ≤ stT160 206 := by
  have hc : ((-789/50000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274861563/250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-789/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c207 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((344129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2029277/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t207 : ((3737012453/78125000000 : ℚ) : ℝ) ≤ stT160 207 := by
  have hc : ((43013/62500 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3737012453/78125000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((43013/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c208 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((39967/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101557/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t208 : ((44337171/640000000 : ℚ) : ℝ) ≤ stT160 208 := by
  have hc : ((7993/8000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44337171/640000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((7993/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c209 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((29893/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1816923/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t209 : ((10338011587/200000000000 : ℚ) : ℝ) ≤ stT160 209 := by
  have hc : ((29891/40000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10338011587/200000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((29891/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c210 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((80213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3726243/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t210 : ((11063536119/2000000000000 : ℚ) : ℝ) ≤ stT160 210 := by
  have hc : ((80163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11063536119/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((80163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c211 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-125727/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5626483/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t211 : ((-86560997173/2000000000000 : ℚ) : ℝ) ≤ stT160 211 := by
  have hc : ((-125737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86560997173/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-125737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c212 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-123871/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7517723/10000000) (δ := 321/40000000) (ψ := -466491/1000000) 160 136
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t212 : ((-340317067727/5000000000000 : ℚ) : ℝ) ≤ stT160 212 := by
  have hc : ((-495509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340317067727/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-495509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c213 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-12731/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157697/250000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t213 : ((-279157646813/5000000000000 : ℚ) : ℝ) ≤ stT160 213 := by
  have hc : ((-407417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279157646813/5000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-407417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c214 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-100771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55429/125000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t214 : ((-8612841807/625000000000 : ℚ) : ℝ) ≤ stT160 214 := by
  have hc : ((-25199/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8612841807/625000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-25199/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c215 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((516697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32119/125000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t215 : ((176175077059/5000000000000 : ℚ) : ℝ) ≤ stT160 215 := by
  have hc : ((516647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176175077059/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((516647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c216 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((191913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8917/125000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t216 : ((130573295939/2000000000000 : ℚ) : ℝ) ≤ stT160 216 := by
  have hc : ((191903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130573295939/2000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((191903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c217 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((22471/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5671/50000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t217 : ((15253454969/250000000000 : ℚ) : ℝ) ≤ stT160 217 := by
  have hc : ((89879/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15253454969/250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((89879/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c218 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((372299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18583/62500) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t218 : ((50423732793/2000000000000 : ℚ) : ℝ) ≤ stT160 218 := by
  have hc : ((372249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50423732793/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((372249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c219 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-171819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120099/250000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t219 : ((-14515190109/625000000000 : ℚ) : ℝ) ≤ stT160 219 := by
  have hc : ((-42961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14515190109/625000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-42961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c220 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-27557/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 165657/250000) (δ := 1617/200000000) (ψ := -466491/1000000) 160 137
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t220 : ((-1486398627/25000000000 : ℚ) : ℝ) ≤ stT160 220 := by
  have hc : ((-440937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1486398627/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-440937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c221 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-972619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7267603/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t221 : ((-654288174237/10000000000000 : ℚ) : ℝ) ≤ stT160 221 := by
  have hc : ((-972669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-654288174237/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-972669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c222 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-576067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5461763/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t222 : ((-386664957369/10000000000000 : ℚ) : ℝ) ≤ stT160 222 := by
  have hc : ((-576117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386664957369/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-576117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c223 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((105001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3664003/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t223 : ((70280332199/10000000000000 : ℚ) : ℝ) ≤ stT160 223 := by
  have hc : ((104951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70280332199/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((104951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c224 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((182971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1874283/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t224 : ((244488541301/5000000000000 : ℚ) : ℝ) ≤ stT160 224 := by
  have hc : ((365917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244488541301/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((365917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c225 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((199863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92523/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t225 : ((66617600049/1000000000000 : ℚ) : ℝ) ≤ stT160 225 := by
  have hc : ((199853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66617600049/1000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((199853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c226 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((156451/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1681297/10000000) (δ := 253/15625000) (ψ := -466491/1000000) 160 138
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t226 : ((10406298879/200000000000 : ℚ) : ℝ) ≤ stT160 226 := by
  have hc : ((156441/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10406298879/200000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((156441/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c227 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((95347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3447317/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t227 : ((31633701903/2500000000000 : ℚ) : ℝ) ≤ stT160 227 := by
  have hc : ((47661/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31633701903/2500000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((47661/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c228 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-244711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5205557/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t228 : ((-158281813/4882812500 : ℚ) : ℝ) ≤ stT160 228 := by
  have hc : ((-7648/15625 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158281813/4882812500 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-7648/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c229 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-936197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6956117/10000000) (δ := 16/1953125) (ψ := -466491/1000000) 160 138
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t229 : ((-618689806293/10000000000000 : ℚ) : ℝ) ≤ stT160 229 := by
  have hc : ((-936247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618689806293/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-936247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c230 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-943413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7008927/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t230 : ((-622101576403/10000000000000 : ℚ) : ℝ) ≤ stT160 230 := by
  have hc : ((-943463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-622101576403/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-943463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c231 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-512961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5273567/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t231 : ((-10548019171/312500000000 : ℚ) : ℝ) ≤ stT160 231 := by
  have hc : ((-513011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10548019171/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-513011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c232 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((30383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3545727/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t232 : ((4985211609/500000000000 : ℚ) : ℝ) ≤ stT160 232 := by
  have hc : ((30373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4985211609/500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((30373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c233 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((372549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1825287/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t233 : ((61012073851/1250000000000 : ℚ) : ℝ) ≤ stT160 233 := by
  have hc : ((93131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61012073851/1250000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((93131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c234 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((998993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112207/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t234 : ((16325725449/250000000000 : ℚ) : ℝ) ≤ stT160 234 := by
  have hc : ((998943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16325725449/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((998943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c235 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((803633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1593553/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t235 : ((65524961403/1250000000000 : ℚ) : ℝ) ≤ stT160 235 := by
  have hc : ((803583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65524961403/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((803583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c236 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((125623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3292073/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t236 : ((638728629/39062500000 : ℚ) : ℝ) ≤ stT160 236 := by
  have hc : ((62799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((638728629/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((62799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c237 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-410097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4983393/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t237 : ((-26641918679/1000000000000 : ℚ) : ℝ) ≤ stT160 237 := by
  have hc : ((-410147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26641918679/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-410147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c238 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-111187/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6667593/10000000) (δ := 1013/125000000) (ψ := -466491/1000000) 160 139
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t238 : ((-72075909423/1250000000000 : ℚ) : ℝ) ≤ stT160 238 := by
  have hc : ((-444773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72075909423/1250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-444773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c239 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-980793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -736321/1000000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t239 : ((-634455352021/10000000000000 : ℚ) : ℝ) ≤ stT160 239 := by
  have hc : ((-980843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634455352021/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-980843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c240 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-649117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113861/200000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t240 : ((-209518000083/5000000000000 : ℚ) : ℝ) ≤ stT160 240 := by
  have hc : ((-649167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209518000083/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-649167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c241 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-10283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80597/200000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t241 : ((-13263836787/5000000000000 : ℚ) : ℝ) ≤ stT160 241 := by
  have hc : ((-20591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13263836787/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-20591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c242 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((582161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237353/1000000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t242 : ((46774365183/1250000000000 : ℚ) : ℝ) ≤ stT160 242 := by
  have hc : ((582111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46774365183/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((582111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c243 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((59897/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14481/200000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t243 : ((614750733/10000000000 : ℚ) : ℝ) ≤ stT160 243 := by
  have hc : ((479151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614750733/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((479151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c244 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((23331/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91867/1000000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t244 : ((7467666337/125000000000 : ℚ) : ℝ) ≤ stT160 244 := by
  have hc : ((93319/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7467666337/125000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((93319/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c245 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((26089/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51093/200000) (δ := 16007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t245 : ((8333019387/250000000000 : ℚ) : ℝ) ≤ stT160 245 := by
  have hc : ((52173/100000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8333019387/250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((52173/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c246 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-102619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418399/1000000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t246 : ((-65459393013/10000000000000 : ℚ) : ℝ) ≤ stT160 246 := by
  have hc : ((-102669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65459393013/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-102669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c247 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-683019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 580671/1000000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t247 : ((-86925311733/2000000000000 : ℚ) : ℝ) ≤ stT160 247 := by
  have hc : ((-683069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86925311733/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-683069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c248 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-61573/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 742287/1000000) (δ := 8007/1000000000) (ψ := -466491/1000000) 160 140
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t248 : ((-312807207609/5000000000000 : ℚ) : ℝ) ≤ stT160 248 := by
  have hc : ((-492609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312807207609/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-492609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c249 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-55683/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6675453/10000000) (δ := 4057/500000000) (ψ := -466491/1000000) 160 141
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t249 : ((-11292700661/200000000000 : ℚ) : ℝ) ≤ stT160 249 := by
  have hc : ((-445489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11292700661/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-445489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_c250 :
    |Real.cos (((160 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-88447/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5072213/10000000) (δ := 4057/500000000) (ψ := -466491/1000000) 160 141
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st160_t250 : ((-6993145049/250000000000 : ℚ) : ℝ) ≤ stT160 250 := by
  have hc : ((-88457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((160 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st160_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6993145049/250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-88457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st160_p1 : ((446551/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT160 (i+1) := by
  rw [Finset.sum_range_one]
  exact st160_t1

theorem st160_p2 : ((489282960107/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT160 (i+1))
      = (∑ i ∈ Finset.range 1, stT160 (i+1)) + stT160 2 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 1
    simpa using h
  have hprev := st160_p1
  have hstep := st160_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p3 : ((6658596820271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT160 (i+1))
      = (∑ i ∈ Finset.range 2, stT160 (i+1)) + stT160 3 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 2
    simpa using h
  have hprev := st160_p2
  have hstep := st160_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p4 : ((9760587929221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT160 (i+1))
      = (∑ i ∈ Finset.range 3, stT160 (i+1)) + stT160 4 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 3
    simpa using h
  have hprev := st160_p3
  have hstep := st160_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p5 : ((3484087517659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT160 (i+1))
      = (∑ i ∈ Finset.range 4, stT160 (i+1)) + stT160 5 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 4
    simpa using h
  have hprev := st160_p4
  have hstep := st160_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p6 : ((12699598588133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT160 (i+1))
      = (∑ i ∈ Finset.range 5, stT160 (i+1)) + stT160 6 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 5
    simpa using h
  have hprev := st160_p5
  have hstep := st160_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p7 : ((2512769152087/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT160 (i+1))
      = (∑ i ∈ Finset.range 6, stT160 (i+1)) + stT160 7 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 6
    simpa using h
  have hprev := st160_p6
  have hstep := st160_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p8 : ((6768234339671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT160 (i+1))
      = (∑ i ∈ Finset.range 7, stT160 (i+1)) + stT160 8 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 7
    simpa using h
  have hprev := st160_p7
  have hstep := st160_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p9 : ((16824885017167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT160 (i+1))
      = (∑ i ∈ Finset.range 8, stT160 (i+1)) + stT160 9 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 8
    simpa using h
  have hprev := st160_p8
  have hstep := st160_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p10 : ((16020822076941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT160 (i+1))
      = (∑ i ∈ Finset.range 9, stT160 (i+1)) + stT160 10 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 9
    simpa using h
  have hprev := st160_p9
  have hstep := st160_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p11 : ((17998271877539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT160 (i+1))
      = (∑ i ∈ Finset.range 10, stT160 (i+1)) + stT160 11 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 10
    simpa using h
  have hprev := st160_p10
  have hstep := st160_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p12 : ((16273977380163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT160 (i+1))
      = (∑ i ∈ Finset.range 11, stT160 (i+1)) + stT160 12 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 11
    simpa using h
  have hprev := st160_p11
  have hstep := st160_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p13 : ((14135230913027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT160 (i+1))
      = (∑ i ∈ Finset.range 12, stT160 (i+1)) + stT160 13 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 12
    simpa using h
  have hprev := st160_p12
  have hstep := st160_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p14 : ((13679106742769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT160 (i+1))
      = (∑ i ∈ Finset.range 13, stT160 (i+1)) + stT160 14 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 13
    simpa using h
  have hprev := st160_p13
  have hstep := st160_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p15 : ((16201659960997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT160 (i+1))
      = (∑ i ∈ Finset.range 14, stT160 (i+1)) + stT160 15 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 14
    simpa using h
  have hprev := st160_p14
  have hstep := st160_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p16 : ((15103619521781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT160 (i+1))
      = (∑ i ∈ Finset.range 15, stT160 (i+1)) + stT160 16 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 15
    simpa using h
  have hprev := st160_p15
  have hstep := st160_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p17 : ((621461725697/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT160 (i+1))
      = (∑ i ∈ Finset.range 16, stT160 (i+1)) + stT160 17 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 16
    simpa using h
  have hprev := st160_p16
  have hstep := st160_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p18 : ((7246128515603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT160 (i+1))
      = (∑ i ∈ Finset.range 17, stT160 (i+1)) + stT160 18 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 17
    simpa using h
  have hprev := st160_p17
  have hstep := st160_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p19 : ((8328314490701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT160 (i+1))
      = (∑ i ∈ Finset.range 18, stT160 (i+1)) + stT160 19 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 18
    simpa using h
  have hprev := st160_p18
  have hstep := st160_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p20 : ((7615923350513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT160 (i+1))
      = (∑ i ∈ Finset.range 19, stT160 (i+1)) + stT160 20 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 19
    simpa using h
  have hprev := st160_p19
  have hstep := st160_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p21 : ((3371406946501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT160 (i+1))
      = (∑ i ∈ Finset.range 20, stT160 (i+1)) + stT160 21 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 20
    simpa using h
  have hprev := st160_p20
  have hstep := st160_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p22 : ((111813083153/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT160 (i+1))
      = (∑ i ∈ Finset.range 21, stT160 (i+1)) + stT160 22 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 21
    simpa using h
  have hprev := st160_p21
  have hstep := st160_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p23 : ((15797089129621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT160 (i+1))
      = (∑ i ∈ Finset.range 22, stT160 (i+1)) + stT160 23 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 22
    simpa using h
  have hprev := st160_p22
  have hstep := st160_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p24 : ((3567586009277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT160 (i+1))
      = (∑ i ∈ Finset.range 23, stT160 (i+1)) + stT160 24 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 23
    simpa using h
  have hprev := st160_p23
  have hstep := st160_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p25 : ((3953557609277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT160 (i+1))
      = (∑ i ∈ Finset.range 24, stT160 (i+1)) + stT160 25 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 24
    simpa using h
  have hprev := st160_p24
  have hstep := st160_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p26 : ((86656648371/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT160 (i+1))
      = (∑ i ∈ Finset.range 25, stT160 (i+1)) + stT160 26 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 25
    simpa using h
  have hprev := st160_p25
  have hstep := st160_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p27 : ((18870726447/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT160 (i+1))
      = (∑ i ∈ Finset.range 26, stT160 (i+1)) + stT160 27 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 26
    simpa using h
  have hprev := st160_p26
  have hstep := st160_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p28 : ((2528873760681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT160 (i+1))
      = (∑ i ∈ Finset.range 27, stT160 (i+1)) + stT160 28 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 27
    simpa using h
  have hprev := st160_p27
  have hstep := st160_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p29 : ((3262187971839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT160 (i+1))
      = (∑ i ∈ Finset.range 28, stT160 (i+1)) + stT160 29 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 28
    simpa using h
  have hprev := st160_p28
  have hstep := st160_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p30 : ((6343142751177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT160 (i+1))
      = (∑ i ∈ Finset.range 29, stT160 (i+1)) + stT160 30 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 29
    simpa using h
  have hprev := st160_p29
  have hstep := st160_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p31 : ((5897651313071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT160 (i+1))
      = (∑ i ∈ Finset.range 30, stT160 (i+1)) + stT160 31 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 30
    simpa using h
  have hprev := st160_p30
  have hstep := st160_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p32 : ((355526040199/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT160 (i+1))
      = (∑ i ∈ Finset.range 31, stT160 (i+1)) + stT160 32 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 31
    simpa using h
  have hprev := st160_p31
  have hstep := st160_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p33 : ((3010033555367/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT160 (i+1))
      = (∑ i ∈ Finset.range 32, stT160 (i+1)) + stT160 33 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 32
    simpa using h
  have hprev := st160_p32
  have hstep := st160_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p34 : ((12635973175003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT160 (i+1))
      = (∑ i ∈ Finset.range 33, stT160 (i+1)) + stT160 34 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 33
    simpa using h
  have hprev := st160_p33
  have hstep := st160_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p35 : ((5993108352547/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT160 (i+1))
      = (∑ i ∈ Finset.range 34, stT160 (i+1)) + stT160 35 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 34
    simpa using h
  have hprev := st160_p34
  have hstep := st160_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p36 : ((23189644920297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT160 (i+1))
      = (∑ i ∈ Finset.range 35, stT160 (i+1)) + stT160 36 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 35
    simpa using h
  have hprev := st160_p35
  have hstep := st160_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p37 : ((248124708499/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT160 (i+1))
      = (∑ i ∈ Finset.range 36, stT160 (i+1)) + stT160 37 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 36
    simpa using h
  have hprev := st160_p36
  have hstep := st160_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p38 : ((4871207914171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT160 (i+1))
      = (∑ i ∈ Finset.range 37, stT160 (i+1)) + stT160 38 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 37
    simpa using h
  have hprev := st160_p37
  have hstep := st160_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p39 : ((23288918024261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT160 (i+1))
      = (∑ i ∈ Finset.range 38, stT160 (i+1)) + stT160 39 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 38
    simpa using h
  have hprev := st160_p38
  have hstep := st160_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p40 : ((24866346674513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT160 (i+1))
      = (∑ i ∈ Finset.range 39, stT160 (i+1)) + stT160 40 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 39
    simpa using h
  have hprev := st160_p39
  have hstep := st160_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p41 : ((23867607414823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT160 (i+1))
      = (∑ i ∈ Finset.range 40, stT160 (i+1)) + stT160 41 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 40
    simpa using h
  have hprev := st160_p40
  have hstep := st160_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p42 : ((23836310056201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT160 (i+1))
      = (∑ i ∈ Finset.range 41, stT160 (i+1)) + stT160 42 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 41
    simpa using h
  have hprev := st160_p41
  have hstep := st160_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p43 : ((1546953170731/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT160 (i+1))
      = (∑ i ∈ Finset.range 42, stT160 (i+1)) + stT160 43 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 42
    simpa using h
  have hprev := st160_p42
  have hstep := st160_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p44 : ((23357135888389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT160 (i+1))
      = (∑ i ∈ Finset.range 43, stT160 (i+1)) + stT160 44 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 43
    simpa using h
  have hprev := st160_p43
  have hstep := st160_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p45 : ((24844767079463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT160 (i+1))
      = (∑ i ∈ Finset.range 44, stT160 (i+1)) + stT160 45 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 44
    simpa using h
  have hprev := st160_p44
  have hstep := st160_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p46 : ((23509793299803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT160 (i+1))
      = (∑ i ∈ Finset.range 45, stT160 (i+1)) + stT160 46 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 45
    simpa using h
  have hprev := st160_p45
  have hstep := st160_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p47 : ((24588895995407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT160 (i+1))
      = (∑ i ∈ Finset.range 46, stT160 (i+1)) + stT160 47 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 46
    simpa using h
  have hprev := st160_p46
  have hstep := st160_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p48 : ((23766829854863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT160 (i+1))
      = (∑ i ∈ Finset.range 47, stT160 (i+1)) + stT160 48 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 47
    simpa using h
  have hprev := st160_p47
  have hstep := st160_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p49 : ((24386092526227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT160 (i+1))
      = (∑ i ∈ Finset.range 48, stT160 (i+1)) + stT160 49 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 48
    simpa using h
  have hprev := st160_p48
  have hstep := st160_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p50 : ((23891068128737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT160 (i+1))
      = (∑ i ∈ Finset.range 49, stT160 (i+1)) + stT160 50 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 49
    simpa using h
  have hprev := st160_p49
  have hstep := st160_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p51 : ((24345718040537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT160 (i+1))
      = (∑ i ∈ Finset.range 50, stT160 (i+1)) + stT160 51 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 50
    simpa using h
  have hprev := st160_p50
  have hstep := st160_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p52 : ((23850093233137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT160 (i+1))
      = (∑ i ∈ Finset.range 51, stT160 (i+1)) + stT160 52 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 51
    simpa using h
  have hprev := st160_p51
  have hstep := st160_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p53 : ((6114745870983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT160 (i+1))
      = (∑ i ∈ Finset.range 52, stT160 (i+1)) + stT160 53 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 52
    simpa using h
  have hprev := st160_p52
  have hstep := st160_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p54 : ((1183957777761/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT160 (i+1))
      = (∑ i ∈ Finset.range 53, stT160 (i+1)) + stT160 54 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 53
    simpa using h
  have hprev := st160_p53
  have hstep := st160_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p55 : ((12330593228263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT160 (i+1))
      = (∑ i ∈ Finset.range 54, stT160 (i+1)) + stT160 55 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 54
    simpa using h
  have hprev := st160_p54
  have hstep := st160_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p56 : ((23486012690893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT160 (i+1))
      = (∑ i ∈ Finset.range 55, stT160 (i+1)) + stT160 56 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 55
    simpa using h
  have hprev := st160_p55
  have hstep := st160_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p57 : ((24787484588773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT160 (i+1))
      = (∑ i ∈ Finset.range 56, stT160 (i+1)) + stT160 57 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 56
    simpa using h
  have hprev := st160_p56
  have hstep := st160_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p58 : ((11746898244489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT160 (i+1))
      = (∑ i ∈ Finset.range 57, stT160 (i+1)) + stT160 58 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 57
    simpa using h
  have hprev := st160_p57
  have hstep := st160_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p59 : ((12291788262771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT160 (i+1))
      = (∑ i ∈ Finset.range 58, stT160 (i+1)) + stT160 59 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 58
    simpa using h
  have hprev := st160_p58
  have hstep := st160_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p60 : ((23920262003547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT160 (i+1))
      = (∑ i ∈ Finset.range 59, stT160 (i+1)) + stT160 60 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 59
    simpa using h
  have hprev := st160_p59
  have hstep := st160_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p61 : ((23974783914091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT160 (i+1))
      = (∑ i ∈ Finset.range 60, stT160 (i+1)) + stT160 61 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 60
    simpa using h
  have hprev := st160_p60
  have hstep := st160_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p62 : ((12290271320533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT160 (i+1))
      = (∑ i ∈ Finset.range 61, stT160 (i+1)) + stT160 62 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 61
    simpa using h
  have hprev := st160_p61
  have hstep := st160_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p63 : ((5867508377717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT160 (i+1))
      = (∑ i ∈ Finset.range 62, stT160 (i+1)) + stT160 63 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 62
    simpa using h
  have hprev := st160_p62
  have hstep := st160_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p64 : ((6177361502717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT160 (i+1))
      = (∑ i ∈ Finset.range 63, stT160 (i+1)) + stT160 64 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 63
    simpa using h
  have hprev := st160_p63
  have hstep := st160_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p65 : ((5959265532311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT160 (i+1))
      = (∑ i ∈ Finset.range 64, stT160 (i+1)) + stT160 65 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 64
    simpa using h
  have hprev := st160_p64
  have hstep := st160_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p66 : ((5984216159091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT160 (i+1))
      = (∑ i ∈ Finset.range 65, stT160 (i+1)) + stT160 66 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 65
    simpa using h
  have hprev := st160_p65
  have hstep := st160_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p67 : ((12340169979349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT160 (i+1))
      = (∑ i ∈ Finset.range 66, stT160 (i+1)) + stT160 67 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 66
    simpa using h
  have hprev := st160_p66
  have hstep := st160_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p68 : ((23480380748729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT160 (i+1))
      = (∑ i ∈ Finset.range 67, stT160 (i+1)) + stT160 68 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 67
    simpa using h
  have hprev := st160_p67
  have hstep := st160_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p69 : ((4886201925229/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT160 (i+1))
      = (∑ i ∈ Finset.range 68, stT160 (i+1)) + stT160 69 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 68
    simpa using h
  have hprev := st160_p68
  have hstep := st160_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p70 : ((24346253547297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT160 (i+1))
      = (∑ i ∈ Finset.range 69, stT160 (i+1)) + stT160 70 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 69
    simpa using h
  have hprev := st160_p69
  have hstep := st160_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p71 : ((23493910275243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT160 (i+1))
      = (∑ i ∈ Finset.range 70, stT160 (i+1)) + stT160 71 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 70
    simpa using h
  have hprev := st160_p70
  have hstep := st160_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p72 : ((12330889071201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT160 (i+1))
      = (∑ i ∈ Finset.range 71, stT160 (i+1)) + stT160 72 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 71
    simpa using h
  have hprev := st160_p71
  have hstep := st160_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p73 : ((12049266291379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT160 (i+1))
      = (∑ i ∈ Finset.range 72, stT160 (i+1)) + stT160 73 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 72
    simpa using h
  have hprev := st160_p72
  have hstep := st160_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p74 : ((2947449484387/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT160 (i+1))
      = (∑ i ∈ Finset.range 73, stT160 (i+1)) + stT160 74 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 73
    simpa using h
  have hprev := st160_p73
  have hstep := st160_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p75 : ((6181678817399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT160 (i+1))
      = (∑ i ∈ Finset.range 74, stT160 (i+1)) + stT160 75 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 74
    simpa using h
  have hprev := st160_p74
  have hstep := st160_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p76 : ((6005242008093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT160 (i+1))
      = (∑ i ∈ Finset.range 75, stT160 (i+1)) + stT160 76 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 75
    simpa using h
  have hprev := st160_p75
  have hstep := st160_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p77 : ((11795189080863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT160 (i+1))
      = (∑ i ∈ Finset.range 76, stT160 (i+1)) + stT160 77 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 76
    simpa using h
  have hprev := st160_p76
  have hstep := st160_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p78 : ((24716202315103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT160 (i+1))
      = (∑ i ∈ Finset.range 77, stT160 (i+1)) + stT160 78 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 77
    simpa using h
  have hprev := st160_p77
  have hstep := st160_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p79 : ((24105434793247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT160 (i+1))
      = (∑ i ∈ Finset.range 78, stT160 (i+1)) + stT160 79 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 78
    simpa using h
  have hprev := st160_p78
  have hstep := st160_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p80 : ((23516045281603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT160 (i+1))
      = (∑ i ∈ Finset.range 79, stT160 (i+1)) + stT160 80 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 79
    simpa using h
  have hprev := st160_p79
  have hstep := st160_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p81 : ((24616476282671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT160 (i+1))
      = (∑ i ∈ Finset.range 80, stT160 (i+1)) + stT160 81 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 80
    simpa using h
  have hprev := st160_p80
  have hstep := st160_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p82 : ((24338909769019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT160 (i+1))
      = (∑ i ∈ Finset.range 81, stT160 (i+1)) + stT160 82 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 81
    simpa using h
  have hprev := st160_p81
  have hstep := st160_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p83 : ((11723599432589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT160 (i+1))
      = (∑ i ∈ Finset.range 82, stT160 (i+1)) + stT160 83 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 82
    simpa using h
  have hprev := st160_p82
  have hstep := st160_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p84 : ((12172977530307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT160 (i+1))
      = (∑ i ∈ Finset.range 83, stT160 (i+1)) + stT160 84 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 83
    simpa using h
  have hprev := st160_p83
  have hstep := st160_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p85 : ((12322848778081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT160 (i+1))
      = (∑ i ∈ Finset.range 84, stT160 (i+1)) + stT160 85 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 84
    simpa using h
  have hprev := st160_p84
  have hstep := st160_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p86 : ((11783771044321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT160 (i+1))
      = (∑ i ∈ Finset.range 85, stT160 (i+1)) + stT160 86 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 85
    simpa using h
  have hprev := st160_p85
  have hstep := st160_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p87 : ((11941886122081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT160 (i+1))
      = (∑ i ∈ Finset.range 86, stT160 (i+1)) + stT160 87 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 86
    simpa using h
  have hprev := st160_p86
  have hstep := st160_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p88 : ((2478844208613/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT160 (i+1))
      = (∑ i ∈ Finset.range 87, stT160 (i+1)) + stT160 88 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 87
    simpa using h
  have hprev := st160_p87
  have hstep := st160_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p89 : ((3004018941637/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT160 (i+1))
      = (∑ i ∈ Finset.range 88, stT160 (i+1)) + stT160 89 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 88
    simpa using h
  have hprev := st160_p88
  have hstep := st160_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p90 : ((23472644239161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT160 (i+1))
      = (∑ i ∈ Finset.range 89, stT160 (i+1)) + stT160 90 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 89
    simpa using h
  have hprev := st160_p89
  have hstep := st160_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p91 : ((24452825420817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT160 (i+1))
      = (∑ i ∈ Finset.range 90, stT160 (i+1)) + stT160 91 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 90
    simpa using h
  have hprev := st160_p90
  have hstep := st160_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p92 : ((24643984124733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT160 (i+1))
      = (∑ i ∈ Finset.range 91, stT160 (i+1)) + stT160 92 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 91
    simpa using h
  have hprev := st160_p91
  have hstep := st160_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p93 : ((23607317286533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT160 (i+1))
      = (∑ i ∈ Finset.range 92, stT160 (i+1)) + stT160 93 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 92
    simpa using h
  have hprev := st160_p92
  have hstep := st160_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p94 : ((11862784336381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT160 (i+1))
      = (∑ i ∈ Finset.range 93, stT160 (i+1)) + stT160 94 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 93
    simpa using h
  have hprev := st160_p93
  have hstep := st160_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p95 : ((12361372709173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT160 (i+1))
      = (∑ i ∈ Finset.range 94, stT160 (i+1)) + stT160 95 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 94
    simpa using h
  have hprev := st160_p94
  have hstep := st160_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p96 : ((1523781286151/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT160 (i+1))
      = (∑ i ∈ Finset.range 95, stT160 (i+1)) + stT160 96 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 95
    simpa using h
  have hprev := st160_p95
  have hstep := st160_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p97 : ((586429412693/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT160 (i+1))
      = (∑ i ∈ Finset.range 96, stT160 (i+1)) + stT160 97 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 96
    simpa using h
  have hprev := st160_p96
  have hstep := st160_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p98 : ((748152648827/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT160 (i+1))
      = (∑ i ∈ Finset.range 97, stT160 (i+1)) + stT160 98 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 97
    simpa using h
  have hprev := st160_p97
  have hstep := st160_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p99 : ((12398040398067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT160 (i+1))
      = (∑ i ∈ Finset.range 98, stT160 (i+1)) + stT160 99 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 98
    simpa using h
  have hprev := st160_p98
  have hstep := st160_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p100 : ((12119736398067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT160 (i+1))
      = (∑ i ∈ Finset.range 99, stT160 (i+1)) + stT160 100 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 99
    simpa using h
  have hprev := st160_p99
  have hstep := st160_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p101 : ((5856175213851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT160 (i+1))
      = (∑ i ∈ Finset.range 100, stT160 (i+1)) + stT160 101 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 100
    simpa using h
  have hprev := st160_p100
  have hstep := st160_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p102 : ((1499850241887/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT160 (i+1))
      = (∑ i ∈ Finset.range 101, stT160 (i+1)) + stT160 102 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 101
    simpa using h
  have hprev := st160_p101
  have hstep := st160_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p103 : ((12403361271903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT160 (i+1))
      = (∑ i ∈ Finset.range 102, stT160 (i+1)) + stT160 103 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 102
    simpa using h
  have hprev := st160_p102
  have hstep := st160_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p104 : ((6066838491189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT160 (i+1))
      = (∑ i ∈ Finset.range 103, stT160 (i+1)) + stT160 104 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 103
    simpa using h
  have hprev := st160_p103
  have hstep := st160_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p105 : ((23431618697683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT160 (i+1))
      = (∑ i ∈ Finset.range 104, stT160 (i+1)) + stT160 105 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 104
    simpa using h
  have hprev := st160_p104
  have hstep := st160_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p106 : ((23887382528513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT160 (i+1))
      = (∑ i ∈ Finset.range 105, stT160 (i+1)) + stT160 106 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 105
    simpa using h
  have hprev := st160_p105
  have hstep := st160_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p107 : ((24770027964289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT160 (i+1))
      = (∑ i ∈ Finset.range 106, stT160 (i+1)) + stT160 107 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 106
    simpa using h
  have hprev := st160_p106
  have hstep := st160_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p108 : ((978048829459/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT160 (i+1))
      = (∑ i ∈ Finset.range 107, stT160 (i+1)) + stT160 108 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 107
    simpa using h
  have hprev := st160_p107
  have hstep := st160_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p109 : ((4704228396933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT160 (i+1))
      = (∑ i ∈ Finset.range 108, stT160 (i+1)) + stT160 109 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 108
    simpa using h
  have hprev := st160_p108
  have hstep := st160_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p110 : ((23646497447653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT160 (i+1))
      = (∑ i ∈ Finset.range 109, stT160 (i+1)) + stT160 110 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 109
    simpa using h
  have hprev := st160_p109
  have hstep := st160_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p111 : ((12297784037183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT160 (i+1))
      = (∑ i ∈ Finset.range 110, stT160 (i+1)) + stT160 111 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 110
    simpa using h
  have hprev := st160_p110
  have hstep := st160_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p112 : ((24714945295373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT160 (i+1))
      = (∑ i ∈ Finset.range 111, stT160 (i+1)) + stT160 112 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 111
    simpa using h
  have hprev := st160_p111
  have hstep := st160_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p113 : ((4761919457283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT160 (i+1))
      = (∑ i ∈ Finset.range 112, stT160 (i+1)) + stT160 113 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 112
    simpa using h
  have hprev := st160_p112
  have hstep := st160_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p114 : ((23413689272011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT160 (i+1))
      = (∑ i ∈ Finset.range 113, stT160 (i+1)) + stT160 114 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 113
    simpa using h
  have hprev := st160_p113
  have hstep := st160_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p115 : ((24178081450891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT160 (i+1))
      = (∑ i ∈ Finset.range 114, stT160 (i+1)) + stT160 115 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 114
    simpa using h
  have hprev := st160_p114
  have hstep := st160_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p116 : ((24841037455267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT160 (i+1))
      = (∑ i ∈ Finset.range 115, stT160 (i+1)) + stT160 116 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 115
    simpa using h
  have hprev := st160_p115
  have hstep := st160_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p117 : ((152098810483/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT160 (i+1))
      = (∑ i ∈ Finset.range 116, stT160 (i+1)) + stT160 117 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 116
    simpa using h
  have hprev := st160_p116
  have hstep := st160_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p118 : ((4695432167391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT160 (i+1))
      = (∑ i ∈ Finset.range 117, stT160 (i+1)) + stT160 118 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 117
    simpa using h
  have hprev := st160_p117
  have hstep := st160_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p119 : ((23612682719181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT160 (i+1))
      = (∑ i ∈ Finset.range 118, stT160 (i+1)) + stT160 119 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 118
    simpa using h
  have hprev := st160_p118
  have hstep := st160_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p120 : ((24522331200951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT160 (i+1))
      = (∑ i ∈ Finset.range 119, stT160 (i+1)) + stT160 120 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 119
    simpa using h
  have hprev := st160_p119
  have hstep := st160_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p121 : ((24813793636761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT160 (i+1))
      = (∑ i ∈ Finset.range 120, stT160 (i+1)) + stT160 121 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 120
    simpa using h
  have hprev := st160_p120
  have hstep := st160_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p122 : ((24056619202053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT160 (i+1))
      = (∑ i ∈ Finset.range 121, stT160 (i+1)) + stT160 122 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 121
    simpa using h
  have hprev := st160_p121
  have hstep := st160_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p123 : ((23382145696963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT160 (i+1))
      = (∑ i ∈ Finset.range 122, stT160 (i+1)) + stT160 123 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 122
    simpa using h
  have hprev := st160_p122
  have hstep := st160_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p124 : ((23773149809467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT160 (i+1))
      = (∑ i ∈ Finset.range 123, stT160 (i+1)) + stT160 124 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 123
    simpa using h
  have hprev := st160_p123
  have hstep := st160_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p125 : ((12327699592931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT160 (i+1))
      = (∑ i ∈ Finset.range 124, stT160 (i+1)) + stT160 125 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 124
    simpa using h
  have hprev := st160_p124
  have hstep := st160_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p126 : ((12385856477401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT160 (i+1))
      = (∑ i ∈ Finset.range 125, stT160 (i+1)) + stT160 126 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 125
    simpa using h
  have hprev := st160_p125
  have hstep := st160_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p127 : ((1497980478167/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT160 (i+1))
      = (∑ i ∈ Finset.range 126, stT160 (i+1)) + stT160 127 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 126
    simpa using h
  have hprev := st160_p126
  have hstep := st160_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p128 : ((730103516257/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT160 (i+1))
      = (∑ i ∈ Finset.range 127, stT160 (i+1)) + stT160 128 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 127
    simpa using h
  have hprev := st160_p127
  have hstep := st160_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p129 : ((11889708796237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT160 (i+1))
      = (∑ i ∈ Finset.range 128, stT160 (i+1)) + stT160 129 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 128
    simpa using h
  have hprev := st160_p128
  have hstep := st160_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p130 : ((4929128259/2000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT160 (i+1))
      = (∑ i ∈ Finset.range 129, stT160 (i+1)) + stT160 130 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 129
    simpa using h
  have hprev := st160_p129
  have hstep := st160_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p131 : ((775269902879/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT160 (i+1))
      = (∑ i ∈ Finset.range 130, stT160 (i+1)) + stT160 131 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 130
    simpa using h
  have hprev := st160_p130
  have hstep := st160_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p132 : ((1503927863641/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT160 (i+1))
      = (∑ i ∈ Finset.range 131, stT160 (i+1)) + stT160 132 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 131
    simpa using h
  have hprev := st160_p131
  have hstep := st160_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p133 : ((11690439272063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT160 (i+1))
      = (∑ i ∈ Finset.range 132, stT160 (i+1)) + stT160 133 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 132
    simpa using h
  have hprev := st160_p132
  have hstep := st160_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p134 : ((11815374885761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT160 (i+1))
      = (∑ i ∈ Finset.range 133, stT160 (i+1)) + stT160 134 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 133
    simpa using h
  have hprev := st160_p133
  have hstep := st160_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p135 : ((12244030176847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT160 (i+1))
      = (∑ i ∈ Finset.range 134, stT160 (i+1)) + stT160 135 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 134
    simpa using h
  have hprev := st160_p134
  have hstep := st160_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p136 : ((12441116566873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT160 (i+1))
      = (∑ i ∈ Finset.range 135, stT160 (i+1)) + stT160 136 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 135
    simpa using h
  have hprev := st160_p135
  have hstep := st160_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p137 : ((12167705774071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT160 (i+1))
      = (∑ i ∈ Finset.range 136, stT160 (i+1)) + stT160 137 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 136
    simpa using h
  have hprev := st160_p136
  have hstep := st160_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p138 : ((23519007563493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT160 (i+1))
      = (∑ i ∈ Finset.range 137, stT160 (i+1)) + stT160 138 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 137
    simpa using h
  have hprev := st160_p137
  have hstep := st160_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p139 : ((23410500441101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT160 (i+1))
      = (∑ i ∈ Finset.range 138, stT160 (i+1)) + stT160 139 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 138
    simpa using h
  have hprev := st160_p138
  have hstep := st160_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p140 : ((24130058640623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT160 (i+1))
      = (∑ i ∈ Finset.range 139, stT160 (i+1)) + stT160 140 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 139
    simpa using h
  have hprev := st160_p139
  have hstep := st160_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p141 : ((4966265576827/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT160 (i+1))
      = (∑ i ∈ Finset.range 140, stT160 (i+1)) + stT160 141 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 140
    simpa using h
  have hprev := st160_p140
  have hstep := st160_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p142 : ((24708640314917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT160 (i+1))
      = (∑ i ∈ Finset.range 141, stT160 (i+1)) + stT160 142 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 141
    simpa using h
  have hprev := st160_p141
  have hstep := st160_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p143 : ((23910028249917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT160 (i+1))
      = (∑ i ∈ Finset.range 142, stT160 (i+1)) + stT160 143 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 142
    simpa using h
  have hprev := st160_p142
  have hstep := st160_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p144 : ((23337622791993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT160 (i+1))
      = (∑ i ∈ Finset.range 143, stT160 (i+1)) + stT160 144 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 143
    simpa using h
  have hprev := st160_p143
  have hstep := st160_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p145 : ((23622461870361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT160 (i+1))
      = (∑ i ∈ Finset.range 144, stT160 (i+1)) + stT160 145 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 144
    simpa using h
  have hprev := st160_p144
  have hstep := st160_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p146 : ((12221988262583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT160 (i+1))
      = (∑ i ∈ Finset.range 145, stT160 (i+1)) + stT160 146 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 145
    simpa using h
  have hprev := st160_p145
  have hstep := st160_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p147 : ((12454696683767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT160 (i+1))
      = (∑ i ∈ Finset.range 146, stT160 (i+1)) + stT160 147 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 146
    simpa using h
  have hprev := st160_p146
  have hstep := st160_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p148 : ((24526043669359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT160 (i+1))
      = (∑ i ∈ Finset.range 147, stT160 (i+1)) + stT160 148 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 147
    simpa using h
  have hprev := st160_p147
  have hstep := st160_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p149 : ((23706798561647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT160 (i+1))
      = (∑ i ∈ Finset.range 148, stT160 (i+1)) + stT160 149 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 148
    simpa using h
  have hprev := st160_p148
  have hstep := st160_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p150 : ((11654511634333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT160 (i+1))
      = (∑ i ∈ Finset.range 149, stT160 (i+1)) + stT160 150 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 149
    simpa using h
  have hprev := st160_p149
  have hstep := st160_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p151 : ((11868674594717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT160 (i+1))
      = (∑ i ∈ Finset.range 150, stT160 (i+1)) + stT160 151 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 150
    simpa using h
  have hprev := st160_p150
  have hstep := st160_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p152 : ((12273889051991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT160 (i+1))
      = (∑ i ∈ Finset.range 151, stT160 (i+1)) + stT160 152 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 151
    simpa using h
  have hprev := st160_p151
  have hstep := st160_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p153 : ((12461231633951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT160 (i+1))
      = (∑ i ∈ Finset.range 152, stT160 (i+1)) + stT160 153 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 152
    simpa using h
  have hprev := st160_p152
  have hstep := st160_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p154 : ((1959528697/800000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT160 (i+1))
      = (∑ i ∈ Finset.range 153, stT160 (i+1)) + stT160 154 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 153
    simpa using h
  have hprev := st160_p153
  have hstep := st160_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p155 : ((1184555198773/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT160 (i+1))
      = (∑ i ∈ Finset.range 154, stT160 (i+1)) + stT160 155 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 154
    simpa using h
  have hprev := st160_p154
  have hstep := st160_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p156 : ((145597320679/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT160 (i+1))
      = (∑ i ∈ Finset.range 155, stT160 (i+1)) + stT160 156 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 155
    simpa using h
  have hprev := st160_p155
  have hstep := st160_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p157 : ((5920538248459/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT160 (i+1))
      = (∑ i ∈ Finset.range 156, stT160 (i+1)) + stT160 157 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 156
    simpa using h
  have hprev := st160_p156
  have hstep := st160_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p158 : ((1529794224501/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT160 (i+1))
      = (∑ i ∈ Finset.range 157, stT160 (i+1)) + stT160 158 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 157
    simpa using h
  have hprev := st160_p157
  have hstep := st160_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p159 : ((6232831415967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT160 (i+1))
      = (∑ i ∈ Finset.range 158, stT160 (i+1)) + stT160 159 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 158
    simpa using h
  have hprev := st160_p158
  have hstep := st160_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p160 : ((6157203908627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT160 (i+1))
      = (∑ i ∈ Finset.range 159, stT160 (i+1)) + stT160 160 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 159
    simpa using h
  have hprev := st160_p159
  have hstep := st160_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p161 : ((2385358394447/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT160 (i+1))
      = (∑ i ∈ Finset.range 160, stT160 (i+1)) + stT160 161 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 160
    simpa using h
  have hprev := st160_p160
  have hstep := st160_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p162 : ((2331148705067/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT160 (i+1))
      = (∑ i ∈ Finset.range 161, stT160 (i+1)) + stT160 162 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 161
    simpa using h
  have hprev := st160_p161
  have hstep := st160_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p163 : ((469697045051/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT160 (i+1))
      = (∑ i ∈ Finset.range 162, stT160 (i+1)) + stT160 163 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 162
    simpa using h
  have hprev := st160_p162
  have hstep := st160_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p164 : ((96852515171/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT160 (i+1))
      = (∑ i ∈ Finset.range 163, stT160 (i+1)) + stT160 164 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 163
    simpa using h
  have hprev := st160_p163
  have hstep := st160_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p165 : ((12426996508669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT160 (i+1))
      = (∑ i ∈ Finset.range 164, stT160 (i+1)) + stT160 165 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 164
    simpa using h
  have hprev := st160_p164
  have hstep := st160_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p166 : ((1553389358943/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT160 (i+1))
      = (∑ i ∈ Finset.range 165, stT160 (i+1)) + stT160 166 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 165
    simpa using h
  have hprev := st160_p165
  have hstep := st160_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p167 : ((302750073927/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT160 (i+1))
      = (∑ i ∈ Finset.range 166, stT160 (i+1)) + stT160 167 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 166
    simpa using h
  have hprev := st160_p166
  have hstep := st160_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p168 : ((2936740250907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT160 (i+1))
      = (∑ i ∈ Finset.range 167, stT160 (i+1)) + stT160 168 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 167
    simpa using h
  have hprev := st160_p167
  have hstep := st160_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p169 : ((5821030486079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT160 (i+1))
      = (∑ i ∈ Finset.range 168, stT160 (i+1)) + stT160 169 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 168
    simpa using h
  have hprev := st160_p168
  have hstep := st160_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p170 : ((5939753061941/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT160 (i+1))
      = (∑ i ∈ Finset.range 169, stT160 (i+1)) + stT160 170 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 169
    simpa using h
  have hprev := st160_p169
  have hstep := st160_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p171 : ((613080357443/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT160 (i+1))
      = (∑ i ∈ Finset.range 170, stT160 (i+1)) + stT160 171 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 170
    simpa using h
  have hprev := st160_p170
  have hstep := st160_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p172 : ((3119407951837/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT160 (i+1))
      = (∑ i ∈ Finset.range 171, stT160 (i+1)) + stT160 172 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 171
    simpa using h
  have hprev := st160_p171
  have hstep := st160_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p173 : ((12356205389859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT160 (i+1))
      = (∑ i ∈ Finset.range 172, stT160 (i+1)) + stT160 173 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 172
    simpa using h
  have hprev := st160_p172
  have hstep := st160_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p174 : ((4798721265037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT160 (i+1))
      = (∑ i ∈ Finset.range 173, stT160 (i+1)) + stT160 174 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 173
    simpa using h
  have hprev := st160_p173
  have hstep := st160_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p175 : ((23366859543853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT160 (i+1))
      = (∑ i ∈ Finset.range 174, stT160 (i+1)) + stT160 175 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 174
    simpa using h
  have hprev := st160_p174
  have hstep := st160_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p176 : ((23317303097277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT160 (i+1))
      = (∑ i ∈ Finset.range 175, stT160 (i+1)) + stT160 176 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 175
    simpa using h
  have hprev := st160_p175
  have hstep := st160_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p177 : ((4775473612301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT160 (i+1))
      = (∑ i ∈ Finset.range 176, stT160 (i+1)) + stT160 177 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 176
    simpa using h
  have hprev := st160_p176
  have hstep := st160_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p178 : ((6153969676803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT160 (i+1))
      = (∑ i ∈ Finset.range 177, stT160 (i+1)) + stT160 178 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 177
    simpa using h
  have hprev := st160_p177
  have hstep := st160_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p179 : ((6244041573783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT160 (i+1))
      = (∑ i ∈ Finset.range 178, stT160 (i+1)) + stT160 179 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 178
    simpa using h
  have hprev := st160_p178
  have hstep := st160_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p180 : ((771684537357/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT160 (i+1))
      = (∑ i ∈ Finset.range 179, stT160 (i+1)) + stT160 180 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 179
    simpa using h
  have hprev := st160_p179
  have hstep := st160_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p181 : ((23982905619879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT160 (i+1))
      = (∑ i ∈ Finset.range 180, stT160 (i+1)) + stT160 181 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 180
    simpa using h
  have hprev := st160_p180
  have hstep := st160_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p182 : ((23365084863629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT160 (i+1))
      = (∑ i ∈ Finset.range 181, stT160 (i+1)) + stT160 182 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 181
    simpa using h
  have hprev := st160_p181
  have hstep := st160_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p183 : ((23284945067387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT160 (i+1))
      = (∑ i ∈ Finset.range 182, stT160 (i+1)) + stT160 183 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 182
    simpa using h
  have hprev := st160_p182
  have hstep := st160_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p184 : ((23794580597923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT160 (i+1))
      = (∑ i ∈ Finset.range 183, stT160 (i+1)) + stT160 184 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 183
    simpa using h
  have hprev := st160_p183
  have hstep := st160_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p185 : ((24528444745019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT160 (i+1))
      = (∑ i ∈ Finset.range 184, stT160 (i+1)) + stT160 185 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 184
    simpa using h
  have hprev := st160_p184
  have hstep := st160_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p186 : ((6242817022951/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT160 (i+1))
      = (∑ i ∈ Finset.range 185, stT160 (i+1)) + stT160 186 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 185
    simpa using h
  have hprev := st160_p185
  have hstep := st160_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p187 : ((24819196215089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT160 (i+1))
      = (∑ i ∈ Finset.range 186, stT160 (i+1)) + stT160 187 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 186
    simpa using h
  have hprev := st160_p186
  have hstep := st160_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p188 : ((24181947037689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT160 (i+1))
      = (∑ i ∈ Finset.range 187, stT160 (i+1)) + stT160 188 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 187
    simpa using h
  have hprev := st160_p187
  have hstep := st160_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p189 : ((23496347129897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT160 (i+1))
      = (∑ i ∈ Finset.range 188, stT160 (i+1)) + stT160 189 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 188
    simpa using h
  have hprev := st160_p188
  have hstep := st160_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p190 : ((23223383506739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT160 (i+1))
      = (∑ i ∈ Finset.range 189, stT160 (i+1)) + stT160 190 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 189
    simpa using h
  have hprev := st160_p189
  have hstep := st160_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p191 : ((23540816144113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT160 (i+1))
      = (∑ i ∈ Finset.range 190, stT160 (i+1)) + stT160 191 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 190
    simpa using h
  have hprev := st160_p190
  have hstep := st160_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p192 : ((3029268056681/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT160 (i+1))
      = (∑ i ∈ Finset.range 191, stT160 (i+1)) + stT160 192 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 191
    simpa using h
  have hprev := st160_p191
  have hstep := st160_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p193 : ((24847737073713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT160 (i+1))
      = (∑ i ∈ Finset.range 192, stT160 (i+1)) + stT160 193 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 192
    simpa using h
  have hprev := st160_p192
  have hstep := st160_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p194 : ((24985994963731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT160 (i+1))
      = (∑ i ∈ Finset.range 193, stT160 (i+1)) + stT160 194 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 193
    simpa using h
  have hprev := st160_p193
  have hstep := st160_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p195 : ((24564763230661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT160 (i+1))
      = (∑ i ∈ Finset.range 194, stT160 (i+1)) + stT160 195 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 194
    simpa using h
  have hprev := st160_p194
  have hstep := st160_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p196 : ((23855889375683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT160 (i+1))
      = (∑ i ∈ Finset.range 195, stT160 (i+1)) + stT160 196 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 195
    simpa using h
  have hprev := st160_p195
  have hstep := st160_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p197 : ((11653333071721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT160 (i+1))
      = (∑ i ∈ Finset.range 196, stT160 (i+1)) + stT160 197 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 196
    simpa using h
  have hprev := st160_p196
  have hstep := st160_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p198 : ((11628461753731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT160 (i+1))
      = (∑ i ∈ Finset.range 197, stT160 (i+1)) + stT160 198 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 197
    simpa using h
  have hprev := st160_p197
  have hstep := st160_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p199 : ((4746560907643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT160 (i+1))
      = (∑ i ∈ Finset.range 198, stT160 (i+1)) + stT160 199 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 198
    simpa using h
  have hprev := st160_p198
  have hstep := st160_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p200 : ((24439496174099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT160 (i+1))
      = (∑ i ∈ Finset.range 199, stT160 (i+1)) + stT160 200 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 199
    simpa using h
  have hprev := st160_p199
  have hstep := st160_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p201 : ((24948154310159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT160 (i+1))
      = (∑ i ∈ Finset.range 200, stT160 (i+1)) + stT160 201 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 200
    simpa using h
  have hprev := st160_p200
  have hstep := st160_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p202 : ((4991241817723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT160 (i+1))
      = (∑ i ∈ Finset.range 201, stT160 (i+1)) + stT160 202 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 201
    simpa using h
  have hprev := st160_p201
  have hstep := st160_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p203 : ((19570601681/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT160 (i+1))
      = (∑ i ∈ Finset.range 202, stT160 (i+1)) + stT160 203 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 202
    simpa using h
  have hprev := st160_p202
  have hstep := st160_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p204 : ((11881544348369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT160 (i+1))
      = (∑ i ∈ Finset.range 203, stT160 (i+1)) + stT160 204 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 203
    simpa using h
  have hprev := st160_p203
  have hstep := st160_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p205 : ((23264800782529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT160 (i+1))
      = (∑ i ∈ Finset.range 204, stT160 (i+1)) + stT160 205 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 204
    simpa using h
  have hprev := st160_p204
  have hstep := st160_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p206 : ((23253806320009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT160 (i+1))
      = (∑ i ∈ Finset.range 205, stT160 (i+1)) + stT160 206 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 205
    simpa using h
  have hprev := st160_p205
  have hstep := st160_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p207 : ((23732143913993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT160 (i+1))
      = (∑ i ∈ Finset.range 206, stT160 (i+1)) + stT160 207 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 206
    simpa using h
  have hprev := st160_p206
  have hstep := st160_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p208 : ((6106228052717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT160 (i+1))
      = (∑ i ∈ Finset.range 207, stT160 (i+1)) + stT160 208 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 207
    simpa using h
  have hprev := st160_p207
  have hstep := st160_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p209 : ((12470906395109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT160 (i+1))
      = (∑ i ∈ Finset.range 208, stT160 (i+1)) + stT160 209 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 208
    simpa using h
  have hprev := st160_p208
  have hstep := st160_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p210 : ((24997130470813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT160 (i+1))
      = (∑ i ∈ Finset.range 209, stT160 (i+1)) + stT160 210 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 209
    simpa using h
  have hprev := st160_p209
  have hstep := st160_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p211 : ((6141081371237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT160 (i+1))
      = (∑ i ∈ Finset.range 210, stT160 (i+1)) + stT160 211 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 210
    simpa using h
  have hprev := st160_p210
  have hstep := st160_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p212 : ((11941845674747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT160 (i+1))
      = (∑ i ∈ Finset.range 211, stT160 (i+1)) + stT160 212 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 211
    simpa using h
  have hprev := st160_p211
  have hstep := st160_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p213 : ((5831344013967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT160 (i+1))
      = (∑ i ∈ Finset.range 212, stT160 (i+1)) + stT160 213 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 212
    simpa using h
  have hprev := st160_p212
  have hstep := st160_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p214 : ((5796892646739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT160 (i+1))
      = (∑ i ∈ Finset.range 213, stT160 (i+1)) + stT160 214 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 213
    simpa using h
  have hprev := st160_p213
  have hstep := st160_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p215 : ((11769960370537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT160 (i+1))
      = (∑ i ∈ Finset.range 214, stT160 (i+1)) + stT160 215 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 214
    simpa using h
  have hprev := st160_p214
  have hstep := st160_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p216 : ((24192787220769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT160 (i+1))
      = (∑ i ∈ Finset.range 215, stT160 (i+1)) + stT160 216 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 215
    simpa using h
  have hprev := st160_p215
  have hstep := st160_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p217 : ((24802925419529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT160 (i+1))
      = (∑ i ∈ Finset.range 216, stT160 (i+1)) + stT160 217 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 216
    simpa using h
  have hprev := st160_p216
  have hstep := st160_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p218 : ((12527522041747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT160 (i+1))
      = (∑ i ∈ Finset.range 217, stT160 (i+1)) + stT160 218 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 217
    simpa using h
  have hprev := st160_p217
  have hstep := st160_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p219 : ((99291204167/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT160 (i+1))
      = (∑ i ∈ Finset.range 218, stT160 (i+1)) + stT160 219 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 218
    simpa using h
  have hprev := st160_p218
  have hstep := st160_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p220 : ((484564831819/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT160 (i+1))
      = (∑ i ∈ Finset.range 219, stT160 (i+1)) + stT160 220 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 219
    simpa using h
  have hprev := st160_p219
  have hstep := st160_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p221 : ((23573953416713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT160 (i+1))
      = (∑ i ∈ Finset.range 220, stT160 (i+1)) + stT160 221 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 220
    simpa using h
  have hprev := st160_p220
  have hstep := st160_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p222 : ((1449205528709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT160 (i+1))
      = (∑ i ∈ Finset.range 221, stT160 (i+1)) + stT160 222 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 221
    simpa using h
  have hprev := st160_p221
  have hstep := st160_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p223 : ((23257568791543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT160 (i+1))
      = (∑ i ∈ Finset.range 222, stT160 (i+1)) + stT160 223 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 222
    simpa using h
  have hprev := st160_p222
  have hstep := st160_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p224 : ((4749309174829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT160 (i+1))
      = (∑ i ∈ Finset.range 223, stT160 (i+1)) + stT160 224 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 223
    simpa using h
  have hprev := st160_p223
  have hstep := st160_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p225 : ((4882544374927/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT160 (i+1))
      = (∑ i ∈ Finset.range 224, stT160 (i+1)) + stT160 225 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 224
    simpa using h
  have hprev := st160_p224
  have hstep := st160_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p226 : ((4986607363717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT160 (i+1))
      = (∑ i ∈ Finset.range 225, stT160 (i+1)) + stT160 226 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 225
    simpa using h
  have hprev := st160_p225
  have hstep := st160_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p227 : ((25059571626197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT160 (i+1))
      = (∑ i ∈ Finset.range 226, stT160 (i+1)) + stT160 227 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 226
    simpa using h
  have hprev := st160_p226
  have hstep := st160_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p228 : ((24735410473173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT160 (i+1))
      = (∑ i ∈ Finset.range 227, stT160 (i+1)) + stT160 228 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 227
    simpa using h
  have hprev := st160_p227
  have hstep := st160_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p229 : ((18841188021/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT160 (i+1))
      = (∑ i ∈ Finset.range 228, stT160 (i+1)) + stT160 229 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 228
    simpa using h
  have hprev := st160_p228
  have hstep := st160_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p230 : ((23494619090477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT160 (i+1))
      = (∑ i ∈ Finset.range 229, stT160 (i+1)) + stT160 230 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 229
    simpa using h
  have hprev := st160_p229
  have hstep := st160_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p231 : ((4631416495401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT160 (i+1))
      = (∑ i ∈ Finset.range 230, stT160 (i+1)) + stT160 231 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 230
    simpa using h
  have hprev := st160_p230
  have hstep := st160_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p232 : ((4651357341837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT160 (i+1))
      = (∑ i ∈ Finset.range 231, stT160 (i+1)) + stT160 232 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 231
    simpa using h
  have hprev := st160_p231
  have hstep := st160_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p233 : ((23744883299993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT160 (i+1))
      = (∑ i ∈ Finset.range 232, stT160 (i+1)) + stT160 233 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 232
    simpa using h
  have hprev := st160_p232
  have hstep := st160_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p234 : ((24397912317953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT160 (i+1))
      = (∑ i ∈ Finset.range 233, stT160 (i+1)) + stT160 234 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 233
    simpa using h
  have hprev := st160_p233
  have hstep := st160_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p235 : ((24922112009177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT160 (i+1))
      = (∑ i ∈ Finset.range 234, stT160 (i+1)) + stT160 235 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 234
    simpa using h
  have hprev := st160_p234
  have hstep := st160_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p236 : ((25085626538201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT160 (i+1))
      = (∑ i ∈ Finset.range 235, stT160 (i+1)) + stT160 236 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 235
    simpa using h
  have hprev := st160_p235
  have hstep := st160_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p237 : ((24819207351411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT160 (i+1))
      = (∑ i ∈ Finset.range 236, stT160 (i+1)) + stT160 237 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 236
    simpa using h
  have hprev := st160_p236
  have hstep := st160_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p238 : ((24242600076027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT160 (i+1))
      = (∑ i ∈ Finset.range 237, stT160 (i+1)) + stT160 238 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 237
    simpa using h
  have hprev := st160_p237
  have hstep := st160_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p239 : ((11804072362003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT160 (i+1))
      = (∑ i ∈ Finset.range 238, stT160 (i+1)) + stT160 239 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 238
    simpa using h
  have hprev := st160_p238
  have hstep := st160_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p240 : ((36232982381/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT160 (i+1))
      = (∑ i ∈ Finset.range 239, stT160 (i+1)) + stT160 240 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 239
    simpa using h
  have hprev := st160_p239
  have hstep := st160_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p241 : ((11581290525133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT160 (i+1))
      = (∑ i ∈ Finset.range 240, stT160 (i+1)) + stT160 241 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 240
    simpa using h
  have hprev := st160_p240
  have hstep := st160_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p242 : ((2353677597173/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT160 (i+1))
      = (∑ i ∈ Finset.range 241, stT160 (i+1)) + stT160 242 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 241
    simpa using h
  have hprev := st160_p241
  have hstep := st160_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p243 : ((2415152670473/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT160 (i+1))
      = (∑ i ∈ Finset.range 242, stT160 (i+1)) + stT160 243 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 242
    simpa using h
  have hprev := st160_p242
  have hstep := st160_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p244 : ((2474894001169/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT160 (i+1))
      = (∑ i ∈ Finset.range 243, stT160 (i+1)) + stT160 244 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 243
    simpa using h
  have hprev := st160_p243
  have hstep := st160_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p245 : ((2508226078717/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT160 (i+1))
      = (∑ i ∈ Finset.range 244, stT160 (i+1)) + stT160 245 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 244
    simpa using h
  have hprev := st160_p244
  have hstep := st160_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p246 : ((25016801394157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT160 (i+1))
      = (∑ i ∈ Finset.range 245, stT160 (i+1)) + stT160 246 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 245
    simpa using h
  have hprev := st160_p245
  have hstep := st160_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p247 : ((6145543708873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT160 (i+1))
      = (∑ i ∈ Finset.range 246, stT160 (i+1)) + stT160 247 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 246
    simpa using h
  have hprev := st160_p246
  have hstep := st160_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p248 : ((11978280210137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT160 (i+1))
      = (∑ i ∈ Finset.range 247, stT160 (i+1)) + stT160 248 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 247
    simpa using h
  have hprev := st160_p247
  have hstep := st160_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p249 : ((2923990673403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT160 (i+1))
      = (∑ i ∈ Finset.range 248, stT160 (i+1)) + stT160 249 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 248
    simpa using h
  have hprev := st160_p248
  have hstep := st160_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_p250 : ((1444512474079/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT160 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT160 (i+1))
      = (∑ i ∈ Finset.range 249, stT160 (i+1)) + stT160 250 := by
    have h := Finset.sum_range_succ (fun i => stT160 (i+1)) 249
    simpa using h
  have hprev := st160_p249
  have hstep := st160_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st160_s250 :
    |Real.sin (((160 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))
      - ((-896899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -5072213/10000000) (δ := 4057/500000000) (ψ := -466491/1000000) 160 141
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 160`** (evaluated boundary). -/
theorem station_160_sign : hardyG ((((160:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 160 250 (by norm_num) (by norm_num)
    ((-466491/1000000 : ℚ) : ℝ)
  have hchain := st160_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT160 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((160 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-466491/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st160_c250
  have hsinb := abs_le.mp st160_s250
  have hbdy_lo : ((7271559403543/81920800000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((160 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ))) / 2
          - ((((160:ℕ)):ℝ))
            * Real.sin (((160 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-466491/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((160:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((160:ℝ) * Real.log (250:ℝ) - ((-466491/1000000 : ℚ) : ℝ))) / 2
        - ((160:ℝ)) * Real.sin ((160:ℝ) * Real.log (250:ℝ) - ((-466491/1000000 : ℚ) : ℝ))
        ≥ ((57486773/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((160:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((57486773/400000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((57486773/400000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((57486773/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((160:ℕ)):ℝ))+1) * (((((160:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((182743496837/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1444512474079/625000000000 : ℚ) : ℝ) + ((7271559403543/81920800000000 : ℚ) : ℝ)
      - ((182743496837/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-466491/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((160:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-466491/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((160:ℕ)):ℝ)))).re
      - Real.sin ((-466491/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((160:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((160:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((160:ℕ)):ℝ))
      = (((((160:ℕ)):ℝ)) * (Real.log ((((160:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((160:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_160
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
  have hθwin : |(((-466491/1000000 : ℚ) : ℝ) + ((29:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((160:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((160:ℕ)):ℝ)))
    (φ := ((-466491/1000000 : ℚ) : ℝ) + ((29:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-466491/1000000 : ℚ) : ℝ) + ((29:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-466491/1000000 : ℚ)) : ℝ) - Real.pi) + ((29:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-466491/1000000 : ℚ)) : ℝ) - Real.pi) 29).1,
    (cos_sin_shift ((((-466491/1000000 : ℚ)) : ℝ) - Real.pi) 29).2]
  exact cos_sin_flip ((-466491/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_160_sign
end AxiomAudit
