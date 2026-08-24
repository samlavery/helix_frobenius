import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 194` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT194 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((194 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))

theorem st194_c1 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((479017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45427/625000) (δ := 201/1000000000) (ψ := -290733/1000000) 194 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t1 : ((29937/31250 : ℚ) : ℝ) ≤ stT194 1 := by
  have hc : ((29937/31250 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29937/31250 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((29937/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c2 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-189389/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1758993/2500000) (δ := 2463/250000000) (ψ := -290733/1000000) 194 21
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t2 : ((-334813302033/500000000000 : ℚ) : ℝ) ≤ stT194 2 := by
  have hc : ((-189399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334813302033/500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-189399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c3 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((195739/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -516977/10000000) (δ := 4923/500000000) (ψ := -290733/1000000) 194 34
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t3 : ((565020886479/1000000000000 : ℚ) : ℝ) ≤ stT194 3 := by
  have hc : ((195729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565020886479/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((195729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c4 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((585637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -590707/2500000) (δ := 981/100000000) (ψ := -290733/1000000) 194 43
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t4 : ((585587/2000000 : ℚ) : ℝ) ≤ stT194 4 := by
  have hc : ((585587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((585587/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((585587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c5 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-16681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163757/400000) (δ := 61/6250000) (ψ := -290733/1000000) 194 50
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t5 : ((-18663900579/625000000000 : ℚ) : ℝ) ≤ stT194 5 := by
  have hc : ((-33387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18663900579/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-33387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c6 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-169691/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2896093/5000000) (δ := 9707/1000000000) (ψ := -290733/1000000) 194 55
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t6 : ((-1385623307581/5000000000000 : ℚ) : ℝ) ≤ stT194 6 := by
  have hc : ((-339407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1385623307581/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-339407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c7 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((346129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2015459/10000000) (δ := 9771/1000000000) (ψ := -290733/1000000) 194 60
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t7 : ((40879684593/156250000000 : ℚ) : ℝ) ≤ stT194 7 := by
  have hc : ((43263/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40879684593/156250000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((43263/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c8 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-3869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 789267/2000000) (δ := 4871/500000000) (ψ := -290733/1000000) 194 64
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t8 : ((-3441842349/1250000000000 : ℚ) : ℝ) ≤ stT194 8 := by
  have hc : ((-1947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3441842349/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-1947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c9 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((381031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760763/10000000) (δ := 9713/1000000000) (ψ := -290733/1000000) 194 68
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t9 : ((635009936499/2500000000000 : ℚ) : ℝ) ≤ stT194 9 := by
  have hc : ((190503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635009936499/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((190503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c10 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((79057/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221519/1000000) (δ := 9811/1000000000) (ψ := -290733/1000000) 194 71
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t10 : ((999921474231/5000000000000 : ℚ) : ℝ) ≤ stT194 10 := by
  have hc : ((316203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999921474231/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((316203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c11 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((864471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316747/10000000) (δ := 9733/1000000000) (ψ := -290733/1000000) 194 74
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t11 : ((2606326994573/10000000000000 : ℚ) : ℝ) ≤ stT194 11 := by
  have hc : ((864421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2606326994573/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((864421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c12 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((639/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1803307/5000000) (δ := 9749/1000000000) (ψ := -290733/1000000) 194 77
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t12 : ((1475129761/40000000000 : ℚ) : ℝ) ≤ stT194 12 := by
  have hc : ((511/4000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1475129761/40000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((511/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c13 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((25753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3798169/10000000) (δ := 4867/500000000) (ψ := -290733/1000000) 194 79
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t13 : ((1114947/78125000 : ℚ) : ℝ) ≤ stT194 13 := by
  have hc : ((804/15625 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1114947/78125000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((804/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c14 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-245583/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7383341/10000000) (δ := 9813/1000000000) (ψ := -290733/1000000) 194 82
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t14 : ((-1312763452083/5000000000000 : ℚ) : ℝ) ≤ stT194 14 := by
  have hc : ((-491191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1312763452083/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-491191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c15 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-267407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5337711/10000000) (δ := 4899/500000000) (ψ := -290733/1000000) 194 84
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t15 : ((-86313310281/625000000000 : ℚ) : ℝ) ≤ stT194 15 := by
  have hc : ((-33429/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86313310281/625000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-33429/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c16 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-573023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1090493/2000000) (δ := 1223/125000000) (ψ := -290733/1000000) 194 86
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t16 : ((-1432683073073/10000000000000 : ℚ) : ℝ) ≤ stT194 16 := by
  have hc : ((-573073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1432683073073/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-573073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c17 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-246987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373273/500000) (δ := 9833/1000000000) (ψ := -290733/1000000) 194 88
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t17 : ((-1198123932643/5000000000000 : ℚ) : ℝ) ≤ stT194 17 := by
  have hc : ((-493999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1198123932643/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-493999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c18 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-61503/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11371/25000) (δ := 9863/1000000000) (ψ := -290733/1000000) 194 89
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t18 : ((-289986896713/5000000000000 : ℚ) : ℝ) ≤ stT194 18 := by
  have hc : ((-123031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289986896713/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-123031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c19 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((966909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322467/5000000) (δ := 1951/200000000) (ψ := -290733/1000000) 194 91
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t19 : ((2218126342863/10000000000000 : ℚ) : ℝ) ≤ stT194 19 := by
  have hc : ((966859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2218126342863/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((966859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c20 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-964263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -718361/1000000) (δ := 9769/1000000000) (ψ := -290733/1000000) 194 93
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t20 : ((-539067360321/2500000000000 : ℚ) : ℝ) ≤ stT194 20 := by
  have hc : ((-964313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-539067360321/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-964313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c21 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((952739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385837/5000000) (δ := 2469/250000000) (ψ := -290733/1000000) 194 94
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t21 : ((1039468488321/5000000000000 : ℚ) : ℝ) ≤ stT194 21 := by
  have hc : ((952689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1039468488321/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((952689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c22 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-497921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 762591/1000000) (δ := 9819/1000000000) (ψ := -290733/1000000) 194 95
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t22 : ((-66351553473/312500000000 : ℚ) : ℝ) ≤ stT194 22 := by
  have hc : ((-248973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66351553473/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-248973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c23 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((627579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2230893/10000000) (δ := 4899/500000000) (ψ := -290733/1000000) 194 97
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t23 : ((163561041147/1250000000000 : ℚ) : ℝ) ≤ stT194 23 := by
  have hc : ((627529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163561041147/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((627529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c24 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((470429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2702549/10000000) (δ := 4949/500000000) (ψ := -290733/1000000) 194 98
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t24 : ((960156900339/10000000000000 : ℚ) : ℝ) ≤ stT194 24 := by
  have hc : ((470379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((960156900339/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((470379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c25 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-911331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849157/1250000) (δ := 9791/1000000000) (ψ := -290733/1000000) 194 99
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t25 : ((-1822762911381/10000000000000 : ℚ) : ℝ) ≤ stT194 25 := by
  have hc : ((-911381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1822762911381/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-911381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c26 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-7757/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5600631/10000000) (δ := 611/62500000) (ψ := -290733/1000000) 194 101
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t26 : ((-60855837441/500000000000 : ℚ) : ℝ) ≤ stT194 26 := by
  have hc : ((-62061/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60855837441/500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-62061/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c27 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((360661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3004549/10000000) (δ := 9869/1000000000) (ψ := -290733/1000000) 194 102
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t27 : ((1387991739/20000000000 : ℚ) : ℝ) ≤ stT194 27 := by
  have hc : ((360611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1387991739/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((360611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c28 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((909103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1074177/10000000) (δ := 9841/1000000000) (ψ := -290733/1000000) 194 103
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t28 : ((858974179283/5000000000000 : ℚ) : ℝ) ≤ stT194 28 := by
  have hc : ((909053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((858974179283/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((909053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c29 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((199101/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11857/500000) (δ := 2437/250000000) (ψ := -290733/1000000) 194 104
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t29 : ((369702629723/2000000000000 : ℚ) : ℝ) ≤ stT194 29 := by
  have hc : ((199091/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369702629723/2000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((199091/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c30 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((185091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242851/2500000) (δ := 2437/250000000) (ψ := -290733/1000000) 194 105
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t30 : ((337909970021/2000000000000 : ℚ) : ℝ) ≤ stT194 30 := by
  have hc : ((185081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337909970021/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((185081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c31 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((178619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 583271/5000000) (δ := 123/12500000) (ψ := -290733/1000000) 194 106
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t31 : ((320791230277/2000000000000 : ℚ) : ℝ) ≤ stT194 31 := by
  have hc : ((178609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320791230277/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((178609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c32 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((470929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 856699/10000000) (δ := 987/100000000) (ψ := -290733/1000000) 194 107
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t32 : ((52028005029/312500000000 : ℚ) : ℝ) ≤ stT194 32 := by
  have hc : ((58863/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52028005029/312500000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((58863/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c33 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((499787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72961/10000000) (δ := 4913/500000000) (ψ := -290733/1000000) 194 108
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t33 : ((54373355957/312500000000 : ℚ) : ℝ) ≤ stT194 33 := by
  have hc : ((249881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54373355957/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((249881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c34 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((894931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1156297/10000000) (δ := 9719/1000000000) (ψ := -290733/1000000) 194 109
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t34 : ((306941498357/2000000000000 : ℚ) : ℝ) ≤ stT194 34 := by
  have hc : ((894881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306941498357/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((894881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c35 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((86753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2805323/10000000) (δ := 2453/250000000) (ψ := -290733/1000000) 194 110
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t35 : ((36655596711/500000000000 : ℚ) : ℝ) ≤ stT194 35 := by
  have hc : ((86743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36655596711/500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((86743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c36 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-180511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4850399/10000000) (δ := 4949/500000000) (ψ := -290733/1000000) 194 111
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t36 : ((-37611674189/625000000000 : ℚ) : ℝ) ≤ stT194 36 := by
  have hc : ((-22567/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37611674189/625000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-22567/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c37 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-972827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908731/1250000) (δ := 9797/1000000000) (ψ := -290733/1000000) 194 112
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t37 : ((-159940005923/1000000000000 : ℚ) : ℝ) ≤ stT194 37 := by
  have hc : ((-972877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159940005923/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-972877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c38 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-128061/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5664229/10000000) (δ := 9797/1000000000) (ψ := -290733/1000000) 194 112
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t38 : ((-41551739453/400000000000 : ℚ) : ℝ) ≤ stT194 38 := by
  have hc : ((-128071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41551739453/400000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-128071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c39 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((521871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2554383/10000000) (δ := 989/100000000) (ψ := -290733/1000000) 194 113
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t39 : ((835582052701/10000000000000 : ℚ) : ℝ) ≤ stT194 39 := by
  have hc : ((521821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((835582052701/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((521821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c40 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((939449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -874447/10000000) (δ := 9783/1000000000) (ψ := -290733/1000000) 194 114
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t40 : ((742659728031/5000000000000 : ℚ) : ℝ) ≤ stT194 40 := by
  have hc : ((939399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((742659728031/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((939399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c41 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-268469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4606499/10000000) (δ := 9727/1000000000) (ψ := -290733/1000000) 194 115
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t41 : ((-209678163011/5000000000000 : ℚ) : ℝ) ≤ stT194 41 := by
  have hc : ((-268519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209678163011/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-268519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c42 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-11907/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7080837/10000000) (δ := 9727/1000000000) (ψ := -290733/1000000) 194 115
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t42 : ((-73495480937/500000000000 : ℚ) : ℝ) ≤ stT194 42 := by
  have hc : ((-95261/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73495480937/500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-95261/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c43 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((55127/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1392583/5000000) (δ := 9769/1000000000) (ψ := -290733/1000000) 194 116
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t43 : ((67246653551/1000000000000 : ℚ) : ℝ) ≤ stT194 43 := by
  have hc : ((220483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67246653551/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((220483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c44 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((11858/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177289/1000000) (δ := 9861/1000000000) (ψ := -290733/1000000) 194 117
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t44 : ((143003370159/1250000000000 : ℚ) : ℝ) ≤ stT194 44 := by
  have hc : ((379431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143003370159/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((379431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c45 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-174649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1316309/2000000) (δ := 4877/500000000) (ψ := -290733/1000000) 194 118
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t45 : ((-32545783401/250000000000 : ℚ) : ℝ) ≤ stT194 45 := by
  have hc : ((-174659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32545783401/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-174659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c46 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-7557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2039111/5000000) (δ := 9849/1000000000) (ψ := -290733/1000000) 194 118
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t46 : ((-2230281413/250000000000 : ℚ) : ℝ) ≤ stT194 46 := by
  have hc : ((-30253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2230281413/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-30253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c47 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((177429/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599593/5000000) (δ := 2439/250000000) (ψ := -290733/1000000) 194 119
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t47 : ((258792046931/2000000000000 : ℚ) : ℝ) ≤ stT194 47 := by
  have hc : ((177419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258792046931/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((177419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c48 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-35787/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5357/8000) (δ := 9863/1000000000) (ψ := -290733/1000000) 194 120
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t48 : ((-3228561479/25000000000 : ℚ) : ℝ) ≤ stT194 48 := by
  have hc : ((-35789/40000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3228561479/25000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-35789/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c49 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((246601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1652031/5000000) (δ := 9863/1000000000) (ψ := -290733/1000000) 194 120
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t49 : ((352215608621/10000000000000 : ℚ) : ℝ) ≤ stT194 49 := by
  have hc : ((246551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352215608621/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((246551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c50 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((504307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325693/1250000) (δ := 9833/1000000000) (ψ := -290733/1000000) 194 121
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t50 : ((713126804741/10000000000000 : ℚ) : ℝ) ≤ stT194 50 := by
  have hc : ((504257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((713126804741/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((504257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c51 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-18841/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6998717/10000000) (δ := 9833/1000000000) (ψ := -290733/1000000) 194 121
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t51 : ((-13192047301/100000000000 : ℚ) : ℝ) ≤ stT194 51 := by
  have hc : ((-9421/10000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13192047301/100000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-9421/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c52 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((960107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 708533/10000000) (δ := 9877/1000000000) (ψ := -290733/1000000) 194 122
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t52 : ((5325436179/40000000000 : ℚ) : ℝ) ≤ stT194 52 := by
  have hc : ((960057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5325436179/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((960057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c53 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-669567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2880527/5000000) (δ := 4909/500000000) (ψ := -290733/1000000) 194 123
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t53 : ((-459894964451/5000000000000 : ℚ) : ℝ) ≤ stT194 53 := by
  have hc : ((-669617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459894964451/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-669617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c54 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((246387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 660923/2000000) (δ := 1957/200000000) (ψ := -290733/1000000) 194 123
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t54 : ((335222040699/10000000000000 : ℚ) : ℝ) ≤ stT194 54 := by
  have hc : ((246337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335222040699/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((246337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c55 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((21047/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -700807/2000000) (δ := 9711/1000000000) (ψ := -290733/1000000) 194 124
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t55 : ((113485305037/5000000000000 : ℚ) : ℝ) ≤ stT194 55 := by
  have hc : ((84163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113485305037/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((84163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c56 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-124909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2617469/5000000) (δ := 2473/250000000) (ψ := -290733/1000000) 194 124
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t56 : ((-333866949801/5000000000000 : ℚ) : ℝ) ≤ stT194 56 := by
  have hc : ((-249843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333866949801/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-249843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c57 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((727937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23609/125000) (δ := 2451/250000000) (ψ := -290733/1000000) 194 125
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t57 : ((241027405971/2500000000000 : ℚ) : ℝ) ≤ stT194 57 := by
  have hc : ((727887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241027405971/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((727887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c58 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-866289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6546303/10000000) (δ := 2451/250000000) (ψ := -290733/1000000) 194 125
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t58 : ((-227511883807/2000000000000 : ℚ) : ℝ) ≤ stT194 58 := by
  have hc : ((-866339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227511883807/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-866339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c59 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((939937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217719/2500000) (δ := 4853/500000000) (ψ := -290733/1000000) 194 126
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t59 : ((1223628546543/10000000000000 : ℚ) : ℝ) ≤ stT194 59 := by
  have hc : ((939887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1223628546543/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((939887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c60 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-973811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7280567/10000000) (δ := 9897/1000000000) (ψ := -290733/1000000) 194 126
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t60 : ((-251449936339/2000000000000 : ℚ) : ℝ) ≤ stT194 60 := by
  have hc : ((-973861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251449936339/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-973861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c61 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((986537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82137/2000000) (δ := 9813/1000000000) (ψ := -290733/1000000) 194 127
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t61 : ((78941649201/625000000000 : ℚ) : ℝ) ≤ stT194 61 := by
  have hc : ((986487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78941649201/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((986487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c62 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-988571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7475657/10000000) (δ := 979/100000000) (ψ := -290733/1000000) 194 127
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t62 : ((-627775323621/5000000000000 : ℚ) : ℝ) ≤ stT194 62 := by
  have hc : ((-988621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-627775323621/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-988621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c63 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((491111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29507/625000) (δ := 243/25000000) (ψ := -290733/1000000) 194 128
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t63 : ((309354960383/2500000000000 : ℚ) : ℝ) ≤ stT194 63 := by
  have hc : ((245543/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309354960383/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((245543/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c64 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-962353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7165813/10000000) (δ := 9883/1000000000) (ψ := -290733/1000000) 194 128
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t64 : ((-1203004712403/10000000000000 : ℚ) : ℝ) ≤ stT194 64 := by
  have hc : ((-962403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1203004712403/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-962403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c65 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((917501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1022613/10000000) (δ := 391/40000000) (ψ := -290733/1000000) 194 129
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t65 : ((1137957595497/10000000000000 : ℚ) : ℝ) ≤ stT194 65 := by
  have hc : ((917451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1137957595497/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((917451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c66 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-20791/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51057/80000) (δ := 2457/250000000) (ψ := -290733/1000000) 194 129
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t66 : ((-20474793927/200000000000 : ℚ) : ℝ) ≤ stT194 66 := by
  have hc : ((-83169/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20474793927/200000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-83169/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c67 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((137467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2032457/10000000) (δ := 1947/200000000) (ψ := -290733/1000000) 194 130
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t67 : ((83965196079/1000000000000 : ℚ) : ℝ) ≤ stT194 67 := by
  have hc : ((137457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83965196079/1000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((137457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c68 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-94187/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2576433/5000000) (δ := 2467/250000000) (ψ := -290733/1000000) 194 130
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t68 : ((-114230723763/2000000000000 : ℚ) : ℝ) ≤ stT194 68 := by
  have hc : ((-94197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114230723763/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-94197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c69 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((179939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3474679/10000000) (δ := 9761/1000000000) (ψ := -290733/1000000) 194 131
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t69 : ((108280405881/5000000000000 : ℚ) : ℝ) ≤ stT194 69 := by
  have hc : ((179889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108280405881/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((179889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c70 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((168453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3503841/10000000) (δ := 4921/500000000) (ψ := -290733/1000000) 194 131
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t70 : ((50319995221/2500000000000 : ℚ) : ℝ) ≤ stT194 70 := by
  have hc : ((168403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50319995221/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((168403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c71 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-530373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332787/625000) (δ := 4927/500000000) (ψ := -290733/1000000) 194 132
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t71 : ((-314748234393/5000000000000 : ℚ) : ℝ) ≤ stT194 71 := by
  have hc : ((-530423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314748234393/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-530423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c72 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((104317/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364691/2500000) (δ := 9749/1000000000) (ψ := -290733/1000000) 194 132
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t72 : ((491725465173/5000000000000 : ℚ) : ℝ) ≤ stT194 72 := by
  have hc : ((417243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((491725465173/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((417243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c73 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-248267/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7559449/10000000) (δ := 9747/1000000000) (ψ := -290733/1000000) 194 133
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t73 : ((-145294653077/1250000000000 : ℚ) : ℝ) ≤ stT194 73 := by
  have hc : ((-496559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145294653077/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-496559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c74 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((115883/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -960733/10000000) (δ := 9747/1000000000) (ψ := -290733/1000000) 194 133
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t74 : ((134703940833/1250000000000 : ℚ) : ℝ) ≤ stT194 74 := by
  have hc : ((463507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134703940833/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((463507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c75 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-18887/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5549471/10000000) (δ := 77/7812500) (ψ := -290733/1000000) 194 133
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t75 : ((-348970272117/5000000000000 : ℚ) : ℝ) ≤ stT194 75 := by
  have hc : ((-302217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348970272117/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-302217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c76 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((19223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3734571/10000000) (δ := 9839/1000000000) (ψ := -290733/1000000) 194 134
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t76 : ((22035941919/2500000000000 : ℚ) : ℝ) ≤ stT194 76 := by
  have hc : ((38421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22035941919/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((38421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c77 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((504357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1302699/5000000) (δ := 2441/250000000) (ψ := -290733/1000000) 194 134
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t77 : ((114942155747/2000000000000 : ℚ) : ℝ) ≤ stT194 77 := by
  have hc : ((504307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114942155747/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((504307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c78 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-229891/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53472/78125) (δ := 9871/1000000000) (ψ := -290733/1000000) 194 135
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t78 : ((-260314675173/2500000000000 : ℚ) : ℝ) ≤ stT194 78 := by
  have hc : ((-459807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260314675173/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-459807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c79 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((38589/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -666001/10000000) (δ := 9871/1000000000) (ψ := -290733/1000000) 194 135
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t79 : ((43413732069/400000000000 : ℚ) : ℝ) ≤ stT194 79 := by
  have hc : ((38587/40000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43413732069/400000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((38587/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c80 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-56719/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5434717/10000000) (δ := 9871/1000000000) (ψ := -290733/1000000) 194 135
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t80 : ((-7927420077/125000000000 : ℚ) : ℝ) ≤ stT194 80 := by
  have hc : ((-14181/25000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7927420077/125000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-14181/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c81 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-16023/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2124167/5000000) (δ := 4889/500000000) (ψ := -290733/1000000) 194 136
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t81 : ((-8905146013/625000000000 : ℚ) : ℝ) ≤ stT194 81 := by
  have hc : ((-64117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8905146013/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-64117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c82 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((388451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212833/1250000) (δ := 393/40000000) (ψ := -290733/1000000) 194 136
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t82 : ((42894465819/500000000000 : ℚ) : ℝ) ≤ stT194 82 := by
  have hc : ((194213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42894465819/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((194213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c83 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-248517/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7581543/10000000) (δ := 393/40000000) (ψ := -290733/1000000) 194 136
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t83 : ((-545593331937/5000000000000 : ℚ) : ℝ) ≤ stT194 83 := by
  have hc : ((-497059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-545593331937/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-497059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c84 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((7501/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2317987/10000000) (δ := 3897/200000000) (ψ := -290733/1000000) 194 137
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t84 : ((65468613267/1000000000000 : ℚ) : ℝ) ≤ stT194 84 := by
  have hc : ((60003/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65468613267/1000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((60003/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c85 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((40147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3421721/10000000) (δ := 4859/500000000) (ψ := -290733/1000000) 194 137
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t85 : ((10883669331/500000000000 : ℚ) : ℝ) ≤ stT194 85 := by
  have hc : ((40137/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10883669331/500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((40137/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c86 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-219859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3306841/5000000) (δ := 153/15625000) (ψ := -290733/1000000) 194 138
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t86 : ((-59273398713/625000000000 : ℚ) : ℝ) ≤ stT194 86 := by
  have hc : ((-439743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59273398713/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-439743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c87 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((920023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503323/5000000) (δ := 9811/1000000000) (ψ := -290733/1000000) 194 138
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t87 : ((61644630811/625000000000 : ℚ) : ℝ) ≤ stT194 87 := by
  have hc : ((919973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61644630811/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((919973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c88 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-60327/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2268137/5000000) (δ := 153/15625000) (ψ := -290733/1000000) 194 138
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t88 : ((-32161074179/1250000000000 : ℚ) : ℝ) ≤ stT194 88 := by
  have hc : ((-120679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32161074179/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-120679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c89 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-5189/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711429/1250000) (δ := 1213/125000000) (ψ := -290733/1000000) 194 139
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t89 : ((-13751884053/200000000000 : ℚ) : ℝ) ≤ stT194 89 := by
  have hc : ((-25947/40000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13751884053/200000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-25947/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c90 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((994071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272381/10000000) (δ := 9899/1000000000) (ψ := -290733/1000000) 194 139
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t90 : ((261947395983/2500000000000 : ℚ) : ℝ) ≤ stT194 90 := by
  have hc : ((994021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261947395983/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((994021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c91 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-447459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271699/2500000) (δ := 19499/1000000000) (ψ := -290733/1000000) 194 139
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t91 : ((-93823394413/2000000000000 : ℚ) : ℝ) ≤ stT194 91 := by
  have hc : ((-447509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93823394413/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-447509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c92 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-529011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2660289/5000000) (δ := 9807/1000000000) (ψ := -290733/1000000) 194 140
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t92 : ((-551584713953/10000000000000 : ℚ) : ℝ) ≤ stT194 92 := by
  have hc : ((-529061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551584713953/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-529061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c93 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((499761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19323/2500000) (δ := 2449/250000000) (ψ := -290733/1000000) 194 140
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t93 : ((64775218117/625000000000 : ℚ) : ℝ) ≤ stT194 93 := by
  have hc : ((62467/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64775218117/625000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((62467/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c94 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-91143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5109929/10000000) (δ := 9807/1000000000) (ψ := -290733/1000000) 194 140
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t94 : ((-47008604783/1000000000000 : ℚ) : ℝ) ≤ stT194 94 := by
  have hc : ((-91153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47008604783/1000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-91153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c95 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-577359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1366429/2500000) (δ := 4857/500000000) (ψ := -290733/1000000) 194 141
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t95 : ((-592409508411/10000000000000 : ℚ) : ℝ) ≤ stT194 95 := by
  have hc : ((-577409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592409508411/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-577409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c96 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((494017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6049/156250) (δ := 9889/1000000000) (ψ := -290733/1000000) 194 141
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t96 : ((3151113219/31250000000 : ℚ) : ℝ) ≤ stT194 96 := by
  have hc : ((61749/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3151113219/31250000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((61749/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c97 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-280901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2319411/5000000) (δ := 9889/1000000000) (ψ := -290733/1000000) 194 141
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t97 : ((-285262754997/10000000000000 : ℚ) : ℝ) ≤ stT194 97 := by
  have hc : ((-280951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285262754997/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-280951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c98 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-152491/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3047369/5000000) (δ := 9821/1000000000) (ψ := -290733/1000000) 194 142
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t98 : ((-154049342653/2000000000000 : ℚ) : ℝ) ≤ stT194 98 := by
  have hc : ((-152501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154049342653/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-152501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c99 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((223081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -146353/1250000) (δ := 9821/1000000000) (ψ := -290733/1000000) 194 142
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t99 : ((448384192069/5000000000000 : ℚ) : ℝ) ≤ stT194 99 := by
  have hc : ((446137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448384192069/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((446137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c100 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((89249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3703571/10000000) (δ := 4891/500000000) (ψ := -290733/1000000) 194 142
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t100 : ((89198910801/10000000000000 : ℚ) : ℝ) ≤ stT194 100 := by
  have hc : ((89199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89198910801/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((89199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c101 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-481857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -448653/625000) (δ := 19/1953125) (ψ := -290733/1000000) 194 143
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t101 : ((-119872725379/1250000000000 : ℚ) : ℝ) ≤ stT194 101 := by
  have hc : ((-240941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119872725379/1250000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-240941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c102 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((573493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2400083/10000000) (δ := 79/8000000) (ψ := -290733/1000000) 194 143
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t102 : ((567792866121/10000000000000 : ℚ) : ℝ) ≤ stT194 102 := by
  have hc : ((573443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567792866121/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((573443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c103 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((595707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1165813/5000000) (δ := 19/1953125) (ψ := -290733/1000000) 194 143
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t103 : ((586918116153/10000000000000 : ℚ) : ℝ) ≤ stT194 103 := by
  have hc : ((595657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((586918116153/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((595657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c104 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-944563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7017647/10000000) (δ := 79/8000000) (ψ := -290733/1000000) 194 143
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t104 : ((-926269560153/10000000000000 : ℚ) : ℝ) ≤ stT194 104 := by
  have hc : ((-944613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-926269560153/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-944613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c105 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-48827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1012277/2500000) (δ := 1967/200000000) (ψ := -290733/1000000) 194 144
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t105 : ((-47699113177/10000000000000 : ℚ) : ℝ) ≤ stT194 105 := by
  have hc : ((-48877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47699113177/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-48877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c106 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((488033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548061/10000000) (δ := 1221/125000000) (ψ := -290733/1000000) 194 144
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t106 : ((11849871257/125000000000 : ℚ) : ℝ) ≤ stT194 106 := by
  have hc : ((61001/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11849871257/125000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((61001/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c107 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-45293/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2551057/5000000) (δ := 1221/125000000) (ψ := -290733/1000000) 194 144
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t107 : ((-21895626313/500000000000 : ℚ) : ℝ) ≤ stT194 107 := by
  have hc : ((-22649/50000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21895626313/500000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-22649/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c108 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-95289/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1218837/2000000) (δ := 9743/1000000000) (ψ := -290733/1000000) 194 145
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t108 : ((-366791798431/5000000000000 : ℚ) : ℝ) ≤ stT194 108 := by
  have hc : ((-381181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366791798431/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-381181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c109 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((796293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -812067/5000000) (δ := 9743/1000000000) (ψ := -290733/1000000) 194 145
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t109 : ((381331123859/5000000000000 : ℚ) : ℝ) ≤ stT194 109 := by
  have hc : ((796243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381331123859/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((796243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c110 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((86767/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350641/1250000) (δ := 493/50000000) (ψ := -290733/1000000) 194 145
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t110 : ((41359751367/1000000000000 : ℚ) : ℝ) ≤ stT194 110 := by
  have hc : ((86757/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41359751367/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((86757/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c111 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-96539/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 719433/1000000) (δ := 9743/1000000000) (ψ := -290733/1000000) 194 145
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t111 : ((-1431804843/15625000000 : ℚ) : ℝ) ≤ stT194 111 := by
  have hc : ((-3017/3125 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1431804843/15625000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-3017/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c112 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-94607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2081931/5000000) (δ := 197/20000000) (ψ := -290733/1000000) 194 146
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t112 : ((-5590158449/625000000000 : ℚ) : ℝ) ≤ stT194 112 := by
  have hc : ((-94657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5590158449/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-94657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c113 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((199653/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147303/10000000) (δ := 197/20000000) (ψ := -290733/1000000) 194 146
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t113 : ((2347602037/25000000000 : ℚ) : ℝ) ≤ stT194 113 := by
  have hc : ((199643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2347602037/25000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((199643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c114 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-98051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1105111/2500000) (δ := 197/20000000) (ψ := -290733/1000000) 194 146
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t114 : ((-11482076067/625000000000 : ℚ) : ℝ) ≤ stT194 114 := by
  have hc : ((-24519/125000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11482076067/625000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-24519/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c115 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-189789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -282067/400000) (δ := 9757/1000000000) (ψ := -290733/1000000) 194 147
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t115 : ((-35397703299/400000000000 : ℚ) : ℝ) ≤ stT194 115 := by
  have hc : ((-189799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35397703299/400000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-189799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c116 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((416669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570509/2000000) (δ := 9757/1000000000) (ψ := -290733/1000000) 194 147
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t116 : ((96705185661/2500000000000 : ℚ) : ℝ) ≤ stT194 116 := by
  have hc : ((416619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96705185661/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((416619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c117 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((173141/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655299/5000000) (δ := 9757/1000000000) (ψ := -290733/1000000) 194 147
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t117 : ((320119219/4000000000 : ℚ) : ℝ) ≤ stT194 117 := by
  have hc : ((173131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320119219/4000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((173131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c118 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-284183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5438287/10000000) (δ := 4923/500000000) (ψ := -290733/1000000) 194 147
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t118 : ((-654086949/12500000000 : ℚ) : ℝ) ≤ stT194 118 := by
  have hc : ((-17763/31250 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-654086949/12500000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-17763/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c119 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-391647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3088429/5000000) (δ := 9739/1000000000) (ψ := -290733/1000000) 194 148
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t119 : ((-44880666341/625000000000 : ℚ) : ℝ) ≤ stT194 119 := by
  have hc : ((-48959/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44880666341/625000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-48959/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c120 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((132403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264779/1250000) (δ := 1233/125000000) (ψ := -290733/1000000) 194 148
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t120 : ((12085759791/200000000000 : ℚ) : ℝ) ≤ stT194 120 := by
  have hc : ((132393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12085759791/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((132393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c121 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((722991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953343/5000000) (δ := 1233/125000000) (ψ := -290733/1000000) 194 148
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t121 : ((65721843369/1000000000000 : ℚ) : ℝ) ≤ stT194 121 := by
  have hc : ((722941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65721843369/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((722941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c122 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-177341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2949239/5000000) (δ := 9739/1000000000) (ψ := -290733/1000000) 194 148
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t122 : ((-160568410053/2500000000000 : ℚ) : ℝ) ≤ stT194 122 := by
  have hc : ((-354707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160568410053/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-354707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c123 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-139129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1170057/2000000) (δ := 1229/125000000) (ψ := -290733/1000000) 194 149
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t123 : ((-12545746213/200000000000 : ℚ) : ℝ) ≤ stT194 123 := by
  have hc : ((-139139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12545746213/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-139139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c124 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((179607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923143/10000000) (δ := 1229/125000000) (ψ := -290733/1000000) 194 149
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t124 : ((161280530457/2500000000000 : ℚ) : ℝ) ≤ stT194 124 := by
  have hc : ((359189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161280530457/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((359189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c125 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((704563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 986237/5000000) (δ := 1229/125000000) (ψ := -290733/1000000) 194 149
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t125 : ((630135449051/10000000000000 : ℚ) : ℝ) ≤ stT194 125 := by
  have hc : ((704513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630135449051/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((704513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c126 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-691833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5837051/10000000) (δ := 1229/125000000) (ψ := -290733/1000000) 194 149
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t126 : ((-616378500093/10000000000000 : ℚ) : ℝ) ≤ stT194 126 := by
  have hc : ((-691883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-616378500093/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-691883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c127 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-747293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3018469/5000000) (δ := 4939/500000000) (ψ := -290733/1000000) 194 150
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t127 : ((-663160042451/10000000000000 : ℚ) : ℝ) ≤ stT194 127 := by
  have hc : ((-747343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-663160042451/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-747343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c128 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((626927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1116493/5000000) (δ := 4939/500000000) (ψ := -290733/1000000) 194 150
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t128 : ((554085923391/10000000000000 : ℚ) : ℝ) ≤ stT194 128 := by
  have hc : ((626877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((554085923391/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((626877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c129 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((815877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1541381/10000000) (δ := 4939/500000000) (ψ := -290733/1000000) 194 150
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t129 : ((14365897643/200000000000 : ℚ) : ℝ) ≤ stT194 129 := by
  have hc : ((815827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14365897643/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((815827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c130 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-129353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5286551/10000000) (δ := 4939/500000000) (ψ := -290733/1000000) 194 150
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t130 : ((-226922352129/5000000000000 : ℚ) : ℝ) ≤ stT194 130 := by
  have hc : ((-258731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226922352129/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-258731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c131 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-896217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3352453/5000000) (δ := 4893/500000000) (ψ := -290733/1000000) 194 151
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t131 : ((-156614591847/2000000000000 : ℚ) : ℝ) ≤ stT194 131 := by
  have hc : ((-896267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156614591847/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-896267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c132 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((356133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120667/400000) (δ := 4893/500000000) (ψ := -290733/1000000) 194 151
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t132 : ((77482592551/2500000000000 : ℚ) : ℝ) ≤ stT194 132 := by
  have hc : ((356083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77482592551/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((356083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c133 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((967033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 643717/10000000) (δ := 4893/500000000) (ψ := -290733/1000000) 194 151
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t133 : ((838479662147/10000000000000 : ℚ) : ℝ) ≤ stT194 133 := by
  have hc : ((966983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((838479662147/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((966983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c134 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-139421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2138341/5000000) (δ := 19417/1000000000) (ψ := -290733/1000000) 194 151
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t134 : ((-120484673299/10000000000000 : ℚ) : ℝ) ≤ stT194 134 := by
  have hc : ((-139471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120484673299/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-139471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c135 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-499967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782533/1000000) (δ := 9893/1000000000) (ψ := -290733/1000000) 194 152
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t135 : ((-53790576837/625000000000 : ℚ) : ℝ) ≤ stT194 135 := by
  have hc : ((-62499/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53790576837/625000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-62499/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c136 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-127251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2122991/5000000) (δ := 971/100000000) (ψ := -290733/1000000) 194 152
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t136 : ((-109159716393/10000000000000 : ℚ) : ℝ) ≤ stT194 136 := by
  have hc : ((-127301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109159716393/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-127301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c137 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((192369/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -692823/10000000) (δ := 9893/1000000000) (ψ := -290733/1000000) 194 152
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t137 : ((164343258163/2000000000000 : ℚ) : ℝ) ≤ stT194 137 := by
  have hc : ((192359/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164343258163/2000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((192359/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c138 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((423243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 708609/2500000) (δ := 971/100000000) (ψ := -290733/1000000) 194 152
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t138 : ((45030697551/1250000000000 : ℚ) : ℝ) ≤ stT194 138 := by
  have hc : ((423193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45030697551/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((423193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c139 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-821317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3168141/5000000) (δ := 9893/1000000000) (ψ := -290733/1000000) 194 152
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t139 : ((-696674454363/10000000000000 : ℚ) : ℝ) ≤ stT194 139 := by
  have hc : ((-821367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-696674454363/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-821367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c140 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-708371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5894959/10000000) (δ := 49/5000000) (ψ := -290733/1000000) 194 153
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t140 : ((-119745110051/2000000000000 : ℚ) : ℝ) ≤ stT194 140 := by
  have hc : ((-708421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119745110051/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-708421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c141 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((559339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122151/500000) (δ := 49/5000000) (ψ := -290733/1000000) 194 153
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t141 : ((471005790639/10000000000000 : ℚ) : ℝ) ≤ stT194 141 := by
  have hc : ((559289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471005790639/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((559289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c142 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((923447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246143/2500000) (δ := 49/5000000) (ψ := -290733/1000000) 194 153
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t142 : ((774897217857/10000000000000 : ℚ) : ℝ) ≤ stT194 142 := by
  have hc : ((923397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((774897217857/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((923397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c143 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-183403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1097027/2500000) (δ := 49/5000000) (ψ := -290733/1000000) 194 153
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t143 : ((-153411287079/10000000000000 : ℚ) : ℝ) ≤ stT194 143 := by
  have hc : ((-183453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153411287079/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-183453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c144 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-999407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7767879/10000000) (δ := 49/5000000) (ψ := -290733/1000000) 194 153
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t144 : ((-416440749819/5000000000000 : ℚ) : ℝ) ≤ stT194 144 := by
  have hc : ((-999457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416440749819/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-999457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c145 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-259651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2291821/5000000) (δ := 9707/1000000000) (ψ := -290733/1000000) 194 154
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t145 : ((-43133998791/2000000000000 : ℚ) : ℝ) ≤ stT194 145 := by
  have hc : ((-259701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43133998791/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-259701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c146 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((109691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -625143/5000000) (δ := 1237/125000000) (ψ := -290733/1000000) 194 154
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t146 : ((72620518019/1000000000000 : ℚ) : ℝ) ≤ stT194 146 := by
  have hc : ((438739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72620518019/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((438739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c147 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((67921/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 515069/2500000) (δ := 9707/1000000000) (ψ := -290733/1000000) 194 154
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t147 : ((7002020747/125000000000 : ℚ) : ℝ) ≤ stT194 147 := by
  have hc : ((16979/25000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7002020747/125000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((16979/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c148 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-8413/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534843/1000000) (δ := 1237/125000000) (ψ := -290733/1000000) 194 154
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t148 : ((-44262951159/1000000000000 : ℚ) : ℝ) ≤ stT194 148 := by
  have hc : ((-269241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44262951159/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-269241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c149 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-119261/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3546747/5000000) (δ := 4907/500000000) (ψ := -290733/1000000) 194 155
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t149 : ((-12213443469/156250000000 : ℚ) : ℝ) ≤ stT194 149 := by
  have hc : ((-477069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12213443469/156250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-477069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c150 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((97/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1924689/5000000) (δ := 9789/1000000000) (ψ := -290733/1000000) 194 155
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t150 : ((158145069/62500000000 : ℚ) : ℝ) ≤ stT194 150 := by
  have hc : ((3099/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158145069/62500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((3099/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c151 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((968739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626747/10000000) (δ := 9789/1000000000) (ψ := -290733/1000000) 194 155
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t151 : ((197076870983/2500000000000 : ℚ) : ℝ) ≤ stT194 151 := by
  have hc : ((968689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197076870983/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((968689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c152 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((257479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2574593/10000000) (δ := 4907/500000000) (ψ := -290733/1000000) 194 155
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t152 : ((104411370789/2500000000000 : ℚ) : ℝ) ≤ stT194 152 := by
  have hc : ((128727/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104411370789/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((128727/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c153 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-333873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1438733/2500000) (δ := 4907/500000000) (ψ := -290733/1000000) 194 155
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t153 : ((-134970419897/2500000000000 : ℚ) : ℝ) ≤ stT194 153 := by
  have hc : ((-166949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134970419897/2500000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-166949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c154 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-182271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3396701/5000000) (δ := 4861/500000000) (ψ := -290733/1000000) 194 156
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t154 : ((-146886222263/2000000000000 : ℚ) : ℝ) ≤ stT194 154 := by
  have hc : ((-182281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146886222263/2000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-182281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c155 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((27221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22839/62500) (δ := 9881/1000000000) (ψ := -290733/1000000) 194 156
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t155 : ((43708768323/5000000000000 : ℚ) : ℝ) ≤ stT194 155 := by
  have hc : ((54417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43708768323/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((54417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c156 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((61073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -535253/10000000) (δ := 4861/500000000) (ψ := -290733/1000000) 194 156
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t156 : ((611187309/7812500000 : ℚ) : ℝ) ≤ stT194 156 := by
  have hc : ((488559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((611187309/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((488559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c157 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((259327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12819/50000) (δ := 4861/500000000) (ψ := -290733/1000000) 194 156
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t157 : ((51736323993/1250000000000 : ℚ) : ℝ) ≤ stT194 157 := by
  have hc : ((129651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51736323993/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((129651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c158 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-63381/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2821581/5000000) (δ := 4861/500000000) (ψ := -290733/1000000) 194 156
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t158 : ((-12606809847/250000000000 : ℚ) : ℝ) ≤ stT194 158 := by
  have hc : ((-31693/50000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12606809847/250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-31693/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c159 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-942869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7004839/10000000) (δ := 9829/1000000000) (ψ := -290733/1000000) 194 157
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t159 : ((-186945949697/2500000000000 : ℚ) : ℝ) ≤ stT194 159 := by
  have hc : ((-942919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186945949697/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-942919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c160 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-3709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3964083/10000000) (δ := 9829/1000000000) (ψ := -290733/1000000) 194 157
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t160 : ((-588421251/500000000000 : ℚ) : ℝ) ≤ stT194 160 := by
  have hc : ((-7443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-588421251/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-7443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c161 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((232451/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -942291/10000000) (δ := 4887/500000000) (ψ := -290733/1000000) 194 157
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t161 : ((36637421247/500000000000 : ℚ) : ℝ) ≤ stT194 161 := by
  have hc : ((464877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36637421247/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((464877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c162 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((84881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2060829/10000000) (δ := 4887/500000000) (ψ := -290733/1000000) 194 157
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t162 : ((133367768663/2500000000000 : ℚ) : ℝ) ≤ stT194 162 := by
  have hc : ((339499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133367768663/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((339499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c163 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-54077/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5045471/10000000) (δ := 9829/1000000000) (ψ := -290733/1000000) 194 157
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t163 : ((-169445201913/5000000000000 : ℚ) : ℝ) ≤ stT194 163 := by
  have hc : ((-216333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169445201913/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-216333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c164 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-998007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962017/1250000) (δ := 9867/1000000000) (ψ := -290733/1000000) 194 158
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t164 : ((-779351771533/10000000000000 : ℚ) : ℝ) ≤ stT194 164 := by
  have hc : ((-998057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-779351771533/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-998057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c165 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-64493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4747821/10000000) (δ := 9867/1000000000) (ψ := -290733/1000000) 194 158
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t165 : ((-50215520997/2000000000000 : ℚ) : ℝ) ≤ stT194 165 := by
  have hc : ((-64503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50215520997/2000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-64503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c166 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((747223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -363461/2000000) (δ := 1217/125000000) (ψ := -290733/1000000) 194 158
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t166 : ((11598366479/200000000000 : ℚ) : ℝ) ≤ stT194 166 := by
  have hc : ((747173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11598366479/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((747173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c167 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((905491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1095653/10000000) (δ := 9867/1000000000) (ψ := -290733/1000000) 194 158
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t167 : ((700651070943/10000000000000 : ℚ) : ℝ) ≤ stT194 167 := by
  have hc : ((905441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((700651070943/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((905441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c168 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-12831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 249447/625000) (δ := 1217/125000000) (ψ := -290733/1000000) 194 158
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t168 : ((-1239827819/625000000000 : ℚ) : ℝ) ≤ stT194 168 := by
  have hc : ((-1607/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1239827819/625000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-1607/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c169 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-184693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 686953/1000000) (δ := 1217/125000000) (ψ := -290733/1000000) 194 158
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t169 : ((-142079273393/2000000000000 : ℚ) : ℝ) ≤ stT194 169 := by
  have hc : ((-184703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142079273393/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-184703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c170 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-73117/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5977079/10000000) (δ := 61/6250000) (ψ := -290733/1000000) 194 159
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t170 : ((-5608201473/100000000000 : ℚ) : ℝ) ≤ stT194 170 := by
  have hc : ((-36561/50000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5608201473/100000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-36561/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c171 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((39059/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626501/2000000) (δ := 9843/1000000000) (ψ := -290733/1000000) 194 159
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t171 : ((119457519709/5000000000000 : ℚ) : ℝ) ≤ stT194 171 := by
  have hc : ((156211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119457519709/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((156211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c172 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((992591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -304519/10000000) (δ := 61/6250000) (ψ := -290733/1000000) 194 159
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t172 : ((189201143043/2500000000000 : ℚ) : ℝ) ≤ stT194 172 := by
  have hc : ((992541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189201143043/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((992541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c173 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((537919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100283/400000) (δ := 9843/1000000000) (ψ := -290733/1000000) 194 159
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t173 : ((81786746533/2000000000000 : ℚ) : ℝ) ≤ stT194 173 := by
  have hc : ((537869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81786746533/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((537869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c174 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-10457/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5302469/10000000) (δ := 61/6250000) (ψ := -290733/1000000) 194 159
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t174 : ((-3964099671/100000000000 : ℚ) : ℝ) ≤ stT194 174 := by
  have hc : ((-5229/10000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3964099671/100000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-5229/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c175 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-995849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1525221/2000000) (δ := 9853/1000000000) (ψ := -290733/1000000) 194 160
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t175 : ((-752828935171/10000000000000 : ℚ) : ℝ) ≤ stT194 175 := by
  have hc : ((-995899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-752828935171/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-995899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c176 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-365559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194503/400000) (δ := 9853/1000000000) (ψ := -290733/1000000) 194 160
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t176 : ((-275588386411/10000000000000 : ℚ) : ℝ) ≤ stT194 176 := by
  have hc : ((-365609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275588386411/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-365609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c177 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((165771/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1057331/5000000) (δ := 9853/1000000000) (ψ := -290733/1000000) 194 160
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t177 : ((124591713491/2500000000000 : ℚ) : ℝ) ≤ stT194 177 := by
  have hc : ((331517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124591713491/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((331517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c178 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((242407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617731/10000000) (δ := 9853/1000000000) (ψ := -290733/1000000) 194 160
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t178 : ((363364383959/5000000000000 : ℚ) : ℝ) ≤ stT194 178 := by
  have hc : ((484789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363364383959/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((484789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c179 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((234649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3334847/10000000) (δ := 39/4000000) (ψ := -290733/1000000) 194 160
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t179 : ((35069500713/2000000000000 : ℚ) : ℝ) ≤ stT194 179 := by
  have hc : ((234599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35069500713/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((234599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c180 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-186813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3018391/5000000) (δ := 39/4000000) (ψ := -290733/1000000) 194 160
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t180 : ((-69625753689/1250000000000 : ℚ) : ℝ) ≤ stT194 180 := by
  have hc : ((-373651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69625753689/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-373651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c181 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-235021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -873023/1250000) (δ := 9857/1000000000) (ψ := -290733/1000000) 194 161
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t181 : ((-69879690153/1000000000000 : ℚ) : ℝ) ≤ stT194 181 := by
  have hc : ((-470067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69879690153/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-470067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c182 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-153407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1078007/2500000) (δ := 9857/1000000000) (ψ := -290733/1000000) 194 161
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t182 : ((-91000001/8000000000 : ℚ) : ℝ) ≤ stT194 182 := by
  have hc : ((-153457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91000001/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-153457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c183 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((394447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1654471/10000000) (δ := 4873/500000000) (ψ := -290733/1000000) 194 161
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t183 : ((145782512631/2500000000000 : ℚ) : ℝ) ≤ stT194 183 := by
  have hc : ((197211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145782512631/2500000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((197211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c184 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((922829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 197717/2000000) (δ := 4873/500000000) (ψ := -290733/1000000) 194 161
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t184 : ((680280983811/10000000000000 : ℚ) : ℝ) ≤ stT194 184 := by
  have hc : ((922779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680280983811/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((922779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c185 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((61773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1808667/5000000) (δ := 9857/1000000000) (ψ := -290733/1000000) 194 161
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t185 : ((5674749259/625000000000 : ℚ) : ℝ) ≤ stT194 185 := by
  have hc : ((15437/125000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5674749259/625000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((15437/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c186 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-796783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97373/156250) (δ := 9857/1000000000) (ψ := -290733/1000000) 194 161
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t186 : ((-146066660397/2500000000000 : ℚ) : ℝ) ≤ stT194 186 := by
  have hc : ((-796833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146066660397/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-796833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c187 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-462191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3437761/5000000) (δ := 4919/500000000) (ψ := -290733/1000000) 194 162
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t187 : ((-42250760121/625000000000 : ℚ) : ℝ) ≤ stT194 187 := by
  have hc : ((-57777/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42250760121/625000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-57777/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c188 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-144247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4288871/10000000) (δ := 1953/200000000) (ψ := -290733/1000000) 194 162
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t188 : ((-4209576381/400000000000 : ℚ) : ℝ) ≤ stT194 188 := by
  have hc : ((-144297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4209576381/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-144297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c189 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((386779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857949/5000000) (δ := 4919/500000000) (ψ := -290733/1000000) 194 162
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t189 : ((4395652587/78125000000 : ℚ) : ℝ) ≤ stT194 189 := by
  have hc : ((193377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4395652587/78125000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((193377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c190 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((471813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 843447/10000000) (δ := 4919/500000000) (ψ := -290733/1000000) 194 162
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t190 : ((21391929443/312500000000 : ℚ) : ℝ) ≤ stT194 190 := by
  have hc : ((117947/125000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21391929443/312500000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((117947/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c191 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((213381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1694703/5000000) (δ := 4919/500000000) (ψ := -290733/1000000) 194 162
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t191 : ((77180382497/5000000000000 : ℚ) : ℝ) ≤ stT194 191 := by
  have hc : ((213331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77180382497/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((213331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c192 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-178993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1480507/2500000) (δ := 1953/200000000) (ψ := -290733/1000000) 194 162
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t192 : ((-32296530321/625000000000 : ℚ) : ℝ) ≤ stT194 192 := by
  have hc : ((-358011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32296530321/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-358011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c193 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-30391/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7266457/10000000) (δ := 617/62500000) (ψ := -290733/1000000) 194 163
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t193 : ((-43754105537/625000000000 : ℚ) : ℝ) ≤ stT194 193 := by
  have hc : ((-486281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43754105537/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-486281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c194 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-327063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4759977/10000000) (δ := 617/62500000) (ψ := -290733/1000000) 194 163
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t194 : ((-234853722367/10000000000000 : ℚ) : ℝ) ≤ stT194 194 := by
  have hc : ((-327113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234853722367/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-327113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c195 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((616459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1133199/5000000) (δ := 617/62500000) (ψ := -290733/1000000) 194 163
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t195 : ((220709557313/5000000000000 : ℚ) : ℝ) ≤ stT194 195 := by
  have hc : ((616409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220709557313/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((616409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c196 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((249081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8577/400000) (δ := 9731/1000000000) (ψ := -290733/1000000) 194 163
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t196 : ((71162357409/1000000000000 : ℚ) : ℝ) ≤ stT194 196 := by
  have hc : ((498137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71162357409/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((498137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c197 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((238721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2682639/10000000) (δ := 617/62500000) (ψ := -290733/1000000) 194 163
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t197 : ((2125796739/62500000000 : ℚ) : ℝ) ≤ stT194 197 := by
  have hc : ((29837/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2125796739/62500000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((29837/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c198 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-465801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5138339/10000000) (δ := 9731/1000000000) (ψ := -290733/1000000) 194 163
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t198 : ((-33106633017/1000000000000 : ℚ) : ℝ) ≤ stT194 198 := by
  have hc : ((-465851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33106633017/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-465851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c199 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-497037/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947709/1250000) (δ := 9731/1000000000) (ψ := -290733/1000000) 194 163
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t199 : ((-88089576171/1250000000000 : ℚ) : ℝ) ≤ stT194 199 := by
  have hc : ((-248531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88089576171/1250000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-248531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c200 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-32489/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5695229/10000000) (δ := 307/31250000) (ψ := -290733/1000000) 194 164
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t200 : ((-45949934181/1000000000000 : ℚ) : ℝ) ≤ stT194 200 := by
  have hc : ((-64983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45949934181/1000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-64983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c201 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((25737/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3276243/10000000) (δ := 307/31250000) (ψ := -290733/1000000) 194 164
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t201 : ((907496877/50000000000 : ℚ) : ℝ) ≤ stT194 201 := by
  have hc : ((6433/25000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((907496877/50000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((6433/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c202 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((235037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869333/10000000) (δ := 9779/1000000000) (ψ := -290733/1000000) 194 164
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t202 : ((330725066253/5000000000000 : ℚ) : ℝ) ≤ stT194 202 := by
  have hc : ((470049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330725066253/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((470049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c203 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((409739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 762871/5000000) (δ := 307/31250000) (ψ := -290733/1000000) 194 164
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t203 : ((71890671867/1250000000000 : ℚ) : ℝ) ≤ stT194 203 := by
  have hc : ((204857/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71890671867/1250000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((204857/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c204 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((7183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 488629/1250000) (δ := 307/31250000) (ψ := -290733/1000000) 194 164
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t204 : ((249704931/500000000000 : ℚ) : ℝ) ≤ stT194 204 := by
  have hc : ((7133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249704931/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((7133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c205 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-202107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3140341/5000000) (δ := 307/31250000) (ψ := -290733/1000000) 194 164
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t205 : ((-282333049009/5000000000000 : ℚ) : ℝ) ≤ stT194 205 := by
  have hc : ((-404239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282333049009/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-404239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c206 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-475441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3533587/5000000) (δ := 9717/1000000000) (ψ := -290733/1000000) 194 165
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t206 : ((-82818332011/1250000000000 : ℚ) : ℝ) ≤ stT194 206 := by
  have hc : ((-237733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82818332011/1250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-237733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c207 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-155673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4718513/10000000) (δ := 9717/1000000000) (ψ := -290733/1000000) 194 165
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t207 : ((-54108869601/2500000000000 : ℚ) : ℝ) ≤ stT194 207 := by
  have hc : ((-77849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54108869601/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-77849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c208 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((3623/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74411/312500) (δ := 4943/500000000) (ψ := -290733/1000000) 194 165
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t208 : ((321520761/8000000000 : ℚ) : ℝ) ≤ stT194 208 := by
  have hc : ((57963/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321520761/8000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((57963/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c209 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((499879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10999/2000000) (δ := 4943/500000000) (ψ := -290733/1000000) 194 165
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t209 : ((86439002439/1250000000000 : ℚ) : ℝ) ≤ stT194 209 := by
  have hc : ((249927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86439002439/1250000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((249927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c210 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((309227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 452011/2000000) (δ := 9717/1000000000) (ψ := -290733/1000000) 194 165
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t210 : ((21336947813/500000000000 : ℚ) : ℝ) ≤ stT194 210 := by
  have hc : ((154601/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21336947813/500000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((154601/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c211 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-252093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35657/78125) (δ := 9717/1000000000) (ψ := -290733/1000000) 194 165
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t211 : ((-173582553347/10000000000000 : ℚ) : ℝ) ≤ stT194 211 := by
  have hc : ((-252143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173582553347/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-252143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c212 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-184313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274289/400000) (δ := 4943/500000000) (ψ := -290733/1000000) 194 165
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t212 : ((-126593589369/2000000000000 : ℚ) : ℝ) ≤ stT194 212 := by
  have hc : ((-184323/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126593589369/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-184323/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c213 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-435333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6568377/10000000) (δ := 9793/1000000000) (ψ := -290733/1000000) 194 166
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t213 : ((-149151256331/2500000000000 : ℚ) : ℝ) ≤ stT194 213 := by
  have hc : ((-217679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149151256331/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-217679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c214 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-7367/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2148343/5000000) (δ := 981/100000000) (ψ := -290733/1000000) 194 166
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t214 : ((-5037687027/500000000000 : ℚ) : ℝ) ≤ stT194 214 := by
  have hc : ((-14739/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5037687027/500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-14739/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c215 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((686417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63613/312500) (δ := 981/100000000) (ψ := -290733/1000000) 194 166
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t215 : ((234049087899/5000000000000 : ℚ) : ℝ) ≤ stT194 215 := by
  have hc : ((686367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234049087899/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((686367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c216 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((199261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107489/5000000) (δ := 981/100000000) (ψ := -290733/1000000) 194 166
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t216 : ((135572970663/2000000000000 : ℚ) : ℝ) ≤ stT194 216 := by
  have hc : ((199251/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135572970663/2000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((199251/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c217 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((34707/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 491029/2000000) (δ := 9793/1000000000) (ψ := -290733/1000000) 194 166
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t217 : ((47117034641/1250000000000 : ℚ) : ℝ) ≤ stT194 217 := by
  have hc : ((277631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47117034641/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((277631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c218 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-29859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4685029/10000000) (δ := 981/100000000) (ψ := -290733/1000000) 194 166
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t218 : ((-1264154319/62500000000 : ℚ) : ℝ) ≤ stT194 218 := by
  have hc : ((-3733/12500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1264154319/62500000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-3733/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c219 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-37151/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6904729/10000000) (δ := 9793/1000000000) (ψ := -290733/1000000) 194 166
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t219 : ((-12552846957/200000000000 : ℚ) : ℝ) ≤ stT194 219 := by
  have hc : ((-37153/40000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12552846957/200000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-37153/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c220 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-437799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6593671/10000000) (δ := 99/10000000) (ψ := -290733/1000000) 194 167
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t220 : ((-23061011/390625000 : ℚ) : ℝ) ≤ stT194 220 := by
  have hc : ((-13682/15625 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23061011/390625000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-13682/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c221 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-92879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4394099/10000000) (δ := 99/10000000) (ψ := -290733/1000000) 194 167
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t221 : ((-7811751549/625000000000 : ℚ) : ℝ) ≤ stT194 221 := by
  have hc : ((-11613/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7811751549/625000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-11613/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c222 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((635757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102259/5000000) (δ := 99/10000000) (ψ := -290733/1000000) 194 167
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t222 : ((106664641823/2500000000000 : ℚ) : ℝ) ≤ stT194 222 := by
  have hc : ((635707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106664641823/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((635707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c223 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((999951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12367/5000000) (δ := 99/10000000) (ψ := -290733/1000000) 194 167
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t223 : ((669582704749/10000000000000 : ℚ) : ℝ) ≤ stT194 223 := by
  have hc : ((999901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((669582704749/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((999901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c224 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((653861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2145301/10000000) (δ := 9703/1000000000) (ψ := -290733/1000000) 194 167
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t224 : ((436845781083/10000000000000 : ℚ) : ℝ) ≤ stT194 224 := by
  have hc : ((653811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436845781083/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((653811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c225 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-150899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 861137/2000000) (δ := 9703/1000000000) (ψ := -290733/1000000) 194 167
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t225 : ((-100632716983/10000000000000 : ℚ) : ℝ) ≤ stT194 225 := by
  have hc : ((-150949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100632716983/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-150949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c226 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-847777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3228221/5000000) (δ := 39/2000000) (ψ := -290733/1000000) 194 167
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t226 : ((-563966889957/10000000000000 : ℚ) : ℝ) ≤ stT194 226 := by
  have hc : ((-847827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563966889957/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-847827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c227 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-956071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3555111/5000000) (δ := 613/62500000) (ψ := -290733/1000000) 194 168
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t227 : ((-158650113651/2500000000000 : ℚ) : ℝ) ≤ stT194 227 := by
  have hc : ((-956121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158650113651/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-956121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c228 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-408259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1244589/2500000) (δ := 613/62500000) (ψ := -290733/1000000) 194 168
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t228 : ((-270409576503/10000000000000 : ℚ) : ℝ) ≤ stT194 228 := by
  have hc : ((-408309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270409576503/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-408309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c229 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((83097/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1427901/5000000) (δ := 613/62500000) (ψ := -290733/1000000) 194 168
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t229 : ((27452692583/1000000000000 : ℚ) : ℝ) ≤ stT194 229 := by
  have hc : ((83087/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27452692583/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((83087/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c230 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((956217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46407/625000) (δ := 1959/200000000) (ψ := -290733/1000000) 194 168
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t230 : ((31523869823/500000000000 : ℚ) : ℝ) ≤ stT194 230 := by
  have hc : ((956167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31523869823/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((956167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c231 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((855311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340403/2500000) (δ := 1959/200000000) (ψ := -290733/1000000) 194 168
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t231 : ((562719830211/10000000000000 : ℚ) : ℝ) ≤ stT194 231 := by
  have hc : ((855261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((562719830211/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((855261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c232 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((187041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1728309/5000000) (δ := 1959/200000000) (ψ := -290733/1000000) 194 168
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t232 : ((30691393803/2500000000000 : ℚ) : ℝ) ≤ stT194 232 := by
  have hc : ((186991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30691393803/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((186991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c233 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-18819/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1385663/2500000) (δ := 613/62500000) (ψ := -290733/1000000) 194 168
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t233 : ((-98638116369/2500000000000 : ℚ) : ℝ) ≤ stT194 233 := by
  have hc : ((-301129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98638116369/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-301129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c234 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-497807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7619761/10000000) (δ := 1959/200000000) (ψ := -290733/1000000) 194 168
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t234 : ((-40680404109/625000000000 : ℚ) : ℝ) ≤ stT194 234 := by
  have hc : ((-62229/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40680404109/625000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-62229/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c235 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-148553/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47031/78125) (δ := 1943/200000000) (ψ := -290733/1000000) 194 169
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t235 : ((-96911953227/2000000000000 : ℚ) : ℝ) ≤ stT194 235 := by
  have hc : ((-148563/200000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96911953227/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-148563/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c236 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-419/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3960513/10000000) (δ := 309/31250000) (ψ := -290733/1000000) 194 169
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t236 : ((-876041781/1000000000000 : ℚ) : ℝ) ≤ stT194 236 := by
  have hc : ((-6729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-876041781/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-6729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c237 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((722133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1909787/10000000) (δ := 1943/200000000) (ψ := -290733/1000000) 194 169
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t237 : ((469042732227/10000000000000 : ℚ) : ℝ) ≤ stT194 237 := by
  have hc : ((722083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469042732227/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((722083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c238 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((4993/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26461/2000000) (δ := 309/31250000) (ψ := -290733/1000000) 194 169
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t238 : ((12945262113/200000000000 : ℚ) : ℝ) ≤ stT194 238 := by
  have hc : ((19971/20000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12945262113/200000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((19971/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c239 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((10119/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1082931/5000000) (δ := 1943/200000000) (ψ := -290733/1000000) 194 169
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t239 : ((104718869209/2500000000000 : ℚ) : ℝ) ≤ stT194 239 := by
  have hc : ((323783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104718869209/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((323783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c240 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-5269/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4190931/10000000) (δ := 1943/200000000) (ψ := -290733/1000000) 194 169
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t240 : ((-3402742707/500000000000 : ℚ) : ℝ) ≤ stT194 240 := by
  have hc : ((-10543/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3402742707/500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-10543/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c241 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-790869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6207561/10000000) (δ := 1943/200000000) (ψ := -290733/1000000) 194 169
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t241 : ((-509476010283/10000000000000 : ℚ) : ℝ) ≤ stT194 241 := by
  have hc : ((-790919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-509476010283/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-790919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c242 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-494771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3746057/5000000) (δ := 4911/500000000) (ψ := -290733/1000000) 194 170
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t242 : ((-3180672387/50000000000 : ℚ) : ℝ) ≤ stT194 242 := by
  have hc : ((-123699/125000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3180672387/50000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-123699/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c243 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-11719/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137303/250000) (δ := 9781/1000000000) (ψ := -290733/1000000) 194 170
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t243 : ((-187959793/5000000000 : ℚ) : ℝ) ≤ stT194 243 := by
  have hc : ((-293/500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187959793/5000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-293/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c244 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((2123/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1750161/5000000) (δ := 9781/1000000000) (ψ := -290733/1000000) 194 170
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t244 : ((1358710517/125000000000 : ℚ) : ℝ) ≤ stT194 244 := by
  have hc : ((16979/100000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1358710517/125000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((16979/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c245 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((410773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189587/1250000) (δ := 9711/500000000) (ψ := -290733/1000000) 194 170
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t245 : ((16401064953/312500000000 : ℚ) : ℝ) ≤ stT194 245 := by
  have hc : ((102687/125000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16401064953/312500000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((102687/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c246 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((491601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 458879/10000000) (δ := 4911/500000000) (ψ := -290733/1000000) 194 170
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t246 : ((4897141559/78125000000 : ℚ) : ℝ) ≤ stT194 246 := by
  have hc : ((61447/62500 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4897141559/78125000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((61447/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c247 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((564829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2426427/10000000) (δ := 4911/500000000) (ψ := -290733/1000000) 194 170
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t247 : ((89839960309/2500000000000 : ℚ) : ℝ) ≤ stT194 247 := by
  have hc : ((564779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89839960309/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((564779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c248 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-91291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4386021/10000000) (δ := 4911/500000000) (ψ := -290733/1000000) 194 170
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t248 : ((-14496437829/1250000000000 : ℚ) : ℝ) ≤ stT194 248 := by
  have hc : ((-22829/125000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14496437829/1250000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-22829/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c249 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-821643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6337709/10000000) (δ := 9781/1000000000) (ψ := -290733/1000000) 194 170
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t249 : ((-20829095857/400000000000 : ℚ) : ℝ) ≤ stT194 249 := by
  have hc : ((-821693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20829095857/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-821693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_c250 :
    |Real.cos (((194 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-246351/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3713163/5000000) (δ := 4937/500000000) (ψ := -290733/1000000) 194 171
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st194_t250 : ((-38953518439/625000000000 : ℚ) : ℝ) ≤ stT194 250 := by
  have hc : ((-492727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((194 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st194_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38953518439/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-492727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st194_p1 : ((29937/31250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT194 (i+1) := by
  rw [Finset.sum_range_one]
  exact st194_t1

theorem st194_p2 : ((144178697967/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT194 (i+1))
      = (∑ i ∈ Finset.range 1, stT194 (i+1)) + stT194 2 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 1
    simpa using h
  have hprev := st194_p1
  have hstep := st194_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p3 : ((853378282413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT194 (i+1))
      = (∑ i ∈ Finset.range 2, stT194 (i+1)) + stT194 3 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 2
    simpa using h
  have hprev := st194_p2
  have hstep := st194_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p4 : ((1146171782413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT194 (i+1))
      = (∑ i ∈ Finset.range 3, stT194 (i+1)) + stT194 4 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 3
    simpa using h
  have hprev := st194_p3
  have hstep := st194_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p5 : ((5581547707433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT194 (i+1))
      = (∑ i ∈ Finset.range 4, stT194 (i+1)) + stT194 5 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 4
    simpa using h
  have hprev := st194_p4
  have hstep := st194_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p6 : ((1048981099963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT194 (i+1))
      = (∑ i ∈ Finset.range 5, stT194 (i+1)) + stT194 6 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 5
    simpa using h
  have hprev := st194_p5
  have hstep := st194_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p7 : ((1376018576707/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT194 (i+1))
      = (∑ i ∈ Finset.range 6, stT194 (i+1)) + stT194 7 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 6
    simpa using h
  have hprev := st194_p6
  have hstep := st194_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p8 : ((686288367179/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT194 (i+1))
      = (∑ i ∈ Finset.range 7, stT194 (i+1)) + stT194 8 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 7
    simpa using h
  have hprev := st194_p7
  have hstep := st194_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p9 : ((676032681043/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT194 (i+1))
      = (∑ i ∈ Finset.range 8, stT194 (i+1)) + stT194 9 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 8
    simpa using h
  have hprev := st194_p8
  have hstep := st194_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p10 : ((7760248284661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT194 (i+1))
      = (∑ i ∈ Finset.range 9, stT194 (i+1)) + stT194 10 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 9
    simpa using h
  have hprev := st194_p9
  have hstep := st194_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p11 : ((3625364712779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT194 (i+1))
      = (∑ i ∈ Finset.range 10, stT194 (i+1)) + stT194 11 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 10
    simpa using h
  have hprev := st194_p10
  have hstep := st194_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p12 : ((3699121200829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT194 (i+1))
      = (∑ i ∈ Finset.range 11, stT194 (i+1)) + stT194 12 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 11
    simpa using h
  have hprev := st194_p11
  have hstep := st194_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p13 : ((3727663844029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT194 (i+1))
      = (∑ i ∈ Finset.range 12, stT194 (i+1)) + stT194 13 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 12
    simpa using h
  have hprev := st194_p12
  have hstep := st194_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p14 : ((16012792315979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT194 (i+1))
      = (∑ i ∈ Finset.range 13, stT194 (i+1)) + stT194 14 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 13
    simpa using h
  have hprev := st194_p13
  have hstep := st194_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p15 : ((14631779351483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT194 (i+1))
      = (∑ i ∈ Finset.range 14, stT194 (i+1)) + stT194 15 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 14
    simpa using h
  have hprev := st194_p14
  have hstep := st194_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p16 : ((1319909627841/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT194 (i+1))
      = (∑ i ∈ Finset.range 15, stT194 (i+1)) + stT194 16 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 15
    simpa using h
  have hprev := st194_p15
  have hstep := st194_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p17 : ((2700712103281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT194 (i+1))
      = (∑ i ∈ Finset.range 16, stT194 (i+1)) + stT194 17 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 16
    simpa using h
  have hprev := st194_p16
  have hstep := st194_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p18 : ((5111437309849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT194 (i+1))
      = (∑ i ∈ Finset.range 17, stT194 (i+1)) + stT194 18 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 17
    simpa using h
  have hprev := st194_p17
  have hstep := st194_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p19 : ((12441000962561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT194 (i+1))
      = (∑ i ∈ Finset.range 18, stT194 (i+1)) + stT194 19 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 18
    simpa using h
  have hprev := st194_p18
  have hstep := st194_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p20 : ((10284731521277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT194 (i+1))
      = (∑ i ∈ Finset.range 19, stT194 (i+1)) + stT194 20 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 19
    simpa using h
  have hprev := st194_p19
  have hstep := st194_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p21 : ((12363668497919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT194 (i+1))
      = (∑ i ∈ Finset.range 20, stT194 (i+1)) + stT194 21 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 20
    simpa using h
  have hprev := st194_p20
  have hstep := st194_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p22 : ((10240418786783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT194 (i+1))
      = (∑ i ∈ Finset.range 21, stT194 (i+1)) + stT194 22 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 21
    simpa using h
  have hprev := st194_p21
  have hstep := st194_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p23 : ((11548907115959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT194 (i+1))
      = (∑ i ∈ Finset.range 22, stT194 (i+1)) + stT194 23 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 22
    simpa using h
  have hprev := st194_p22
  have hstep := st194_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p24 : ((6254532008149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT194 (i+1))
      = (∑ i ∈ Finset.range 23, stT194 (i+1)) + stT194 24 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 23
    simpa using h
  have hprev := st194_p23
  have hstep := st194_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p25 : ((10686301104917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT194 (i+1))
      = (∑ i ∈ Finset.range 24, stT194 (i+1)) + stT194 25 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 24
    simpa using h
  have hprev := st194_p24
  have hstep := st194_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p26 : ((9469184356097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT194 (i+1))
      = (∑ i ∈ Finset.range 25, stT194 (i+1)) + stT194 26 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 25
    simpa using h
  have hprev := st194_p25
  have hstep := st194_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p27 : ((10163180225597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT194 (i+1))
      = (∑ i ∈ Finset.range 26, stT194 (i+1)) + stT194 27 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 26
    simpa using h
  have hprev := st194_p26
  have hstep := st194_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p28 : ((11881128584163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT194 (i+1))
      = (∑ i ∈ Finset.range 27, stT194 (i+1)) + stT194 28 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 27
    simpa using h
  have hprev := st194_p27
  have hstep := st194_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p29 : ((6864820866389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT194 (i+1))
      = (∑ i ∈ Finset.range 28, stT194 (i+1)) + stT194 29 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 28
    simpa using h
  have hprev := st194_p28
  have hstep := st194_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p30 : ((15419191582883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT194 (i+1))
      = (∑ i ∈ Finset.range 29, stT194 (i+1)) + stT194 30 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 29
    simpa using h
  have hprev := st194_p29
  have hstep := st194_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p31 : ((4255786933567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT194 (i+1))
      = (∑ i ∈ Finset.range 30, stT194 (i+1)) + stT194 31 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 30
    simpa using h
  have hprev := st194_p30
  have hstep := st194_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p32 : ((4672010973799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT194 (i+1))
      = (∑ i ∈ Finset.range 31, stT194 (i+1)) + stT194 32 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 31
    simpa using h
  have hprev := st194_p31
  have hstep := st194_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p33 : ((1021399564291/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT194 (i+1))
      = (∑ i ∈ Finset.range 32, stT194 (i+1)) + stT194 33 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 32
    simpa using h
  have hprev := st194_p32
  have hstep := st194_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p34 : ((4392539755521/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT194 (i+1))
      = (∑ i ∈ Finset.range 33, stT194 (i+1)) + stT194 34 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 33
    simpa using h
  have hprev := st194_p33
  have hstep := st194_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p35 : ((907832428473/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT194 (i+1))
      = (∑ i ∈ Finset.range 34, stT194 (i+1)) + stT194 35 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 34
    simpa using h
  have hprev := st194_p34
  have hstep := st194_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p36 : ((22094023924801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT194 (i+1))
      = (∑ i ∈ Finset.range 35, stT194 (i+1)) + stT194 36 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 35
    simpa using h
  have hprev := st194_p35
  have hstep := st194_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p37 : ((20494623865571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT194 (i+1))
      = (∑ i ∈ Finset.range 36, stT194 (i+1)) + stT194 37 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 36
    simpa using h
  have hprev := st194_p36
  have hstep := st194_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p38 : ((9727915189623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT194 (i+1))
      = (∑ i ∈ Finset.range 37, stT194 (i+1)) + stT194 38 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 37
    simpa using h
  have hprev := st194_p37
  have hstep := st194_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p39 : ((20291412431947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT194 (i+1))
      = (∑ i ∈ Finset.range 38, stT194 (i+1)) + stT194 39 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 38
    simpa using h
  have hprev := st194_p38
  have hstep := st194_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p40 : ((21776731888009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT194 (i+1))
      = (∑ i ∈ Finset.range 39, stT194 (i+1)) + stT194 40 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 39
    simpa using h
  have hprev := st194_p39
  have hstep := st194_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p41 : ((21357375561987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT194 (i+1))
      = (∑ i ∈ Finset.range 40, stT194 (i+1)) + stT194 41 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 40
    simpa using h
  have hprev := st194_p40
  have hstep := st194_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p42 : ((19887465943247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT194 (i+1))
      = (∑ i ∈ Finset.range 41, stT194 (i+1)) + stT194 42 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 41
    simpa using h
  have hprev := st194_p41
  have hstep := st194_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p43 : ((20559932478757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT194 (i+1))
      = (∑ i ∈ Finset.range 42, stT194 (i+1)) + stT194 43 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 42
    simpa using h
  have hprev := st194_p42
  have hstep := st194_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p44 : ((21703959440029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT194 (i+1))
      = (∑ i ∈ Finset.range 43, stT194 (i+1)) + stT194 44 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 43
    simpa using h
  have hprev := st194_p43
  have hstep := st194_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p45 : ((20402128103989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT194 (i+1))
      = (∑ i ∈ Finset.range 44, stT194 (i+1)) + stT194 45 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 44
    simpa using h
  have hprev := st194_p44
  have hstep := st194_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p46 : ((20312916847469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT194 (i+1))
      = (∑ i ∈ Finset.range 45, stT194 (i+1)) + stT194 46 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 45
    simpa using h
  have hprev := st194_p45
  have hstep := st194_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p47 : ((5401719270531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT194 (i+1))
      = (∑ i ∈ Finset.range 46, stT194 (i+1)) + stT194 47 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 46
    simpa using h
  have hprev := st194_p46
  have hstep := st194_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p48 : ((5078863122631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT194 (i+1))
      = (∑ i ∈ Finset.range 47, stT194 (i+1)) + stT194 48 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 47
    simpa using h
  have hprev := st194_p47
  have hstep := st194_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p49 : ((4133533619829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT194 (i+1))
      = (∑ i ∈ Finset.range 48, stT194 (i+1)) + stT194 49 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 48
    simpa using h
  have hprev := st194_p48
  have hstep := st194_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p50 : ((10690397451943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT194 (i+1))
      = (∑ i ∈ Finset.range 49, stT194 (i+1)) + stT194 50 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 49
    simpa using h
  have hprev := st194_p49
  have hstep := st194_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p51 : ((10030795086893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT194 (i+1))
      = (∑ i ∈ Finset.range 50, stT194 (i+1)) + stT194 51 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 50
    simpa using h
  have hprev := st194_p50
  have hstep := st194_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p52 : ((2674118652317/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT194 (i+1))
      = (∑ i ∈ Finset.range 51, stT194 (i+1)) + stT194 52 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 51
    simpa using h
  have hprev := st194_p51
  have hstep := st194_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p53 : ((10236579644817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT194 (i+1))
      = (∑ i ∈ Finset.range 52, stT194 (i+1)) + stT194 53 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 52
    simpa using h
  have hprev := st194_p52
  have hstep := st194_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p54 : ((20808381330333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT194 (i+1))
      = (∑ i ∈ Finset.range 53, stT194 (i+1)) + stT194 54 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 53
    simpa using h
  have hprev := st194_p53
  have hstep := st194_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p55 : ((21035351940407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT194 (i+1))
      = (∑ i ∈ Finset.range 54, stT194 (i+1)) + stT194 55 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 54
    simpa using h
  have hprev := st194_p54
  have hstep := st194_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p56 : ((4073523608161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT194 (i+1))
      = (∑ i ∈ Finset.range 55, stT194 (i+1)) + stT194 56 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 55
    simpa using h
  have hprev := st194_p55
  have hstep := st194_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p57 : ((21331727664689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT194 (i+1))
      = (∑ i ∈ Finset.range 56, stT194 (i+1)) + stT194 57 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 56
    simpa using h
  have hprev := st194_p56
  have hstep := st194_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p58 : ((10097084122827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT194 (i+1))
      = (∑ i ∈ Finset.range 57, stT194 (i+1)) + stT194 58 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 57
    simpa using h
  have hprev := st194_p57
  have hstep := st194_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p59 : ((21417796792197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT194 (i+1))
      = (∑ i ∈ Finset.range 58, stT194 (i+1)) + stT194 59 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 58
    simpa using h
  have hprev := st194_p58
  have hstep := st194_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p60 : ((10080273555251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT194 (i+1))
      = (∑ i ∈ Finset.range 59, stT194 (i+1)) + stT194 60 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 59
    simpa using h
  have hprev := st194_p59
  have hstep := st194_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p61 : ((10711806748859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT194 (i+1))
      = (∑ i ∈ Finset.range 60, stT194 (i+1)) + stT194 61 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 60
    simpa using h
  have hprev := st194_p60
  have hstep := st194_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p62 : ((5042015712619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT194 (i+1))
      = (∑ i ∈ Finset.range 61, stT194 (i+1)) + stT194 62 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 61
    simpa using h
  have hprev := st194_p61
  have hstep := st194_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p63 : ((2675685336501/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT194 (i+1))
      = (∑ i ∈ Finset.range 62, stT194 (i+1)) + stT194 63 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 62
    simpa using h
  have hprev := st194_p62
  have hstep := st194_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p64 : ((4040495595921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT194 (i+1))
      = (∑ i ∈ Finset.range 63, stT194 (i+1)) + stT194 64 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 63
    simpa using h
  have hprev := st194_p63
  have hstep := st194_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p65 : ((10670217787551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT194 (i+1))
      = (∑ i ∈ Finset.range 64, stT194 (i+1)) + stT194 65 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 64
    simpa using h
  have hprev := st194_p64
  have hstep := st194_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p66 : ((634896746211/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT194 (i+1))
      = (∑ i ∈ Finset.range 65, stT194 (i+1)) + stT194 66 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 65
    simpa using h
  have hprev := st194_p65
  have hstep := st194_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p67 : ((10578173919771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT194 (i+1))
      = (∑ i ∈ Finset.range 66, stT194 (i+1)) + stT194 67 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 66
    simpa using h
  have hprev := st194_p66
  have hstep := st194_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p68 : ((20585194220727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT194 (i+1))
      = (∑ i ∈ Finset.range 67, stT194 (i+1)) + stT194 68 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 67
    simpa using h
  have hprev := st194_p67
  have hstep := st194_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p69 : ((20801755032489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT194 (i+1))
      = (∑ i ∈ Finset.range 68, stT194 (i+1)) + stT194 69 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 68
    simpa using h
  have hprev := st194_p68
  have hstep := st194_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p70 : ((21003035013373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT194 (i+1))
      = (∑ i ∈ Finset.range 69, stT194 (i+1)) + stT194 70 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 69
    simpa using h
  have hprev := st194_p69
  have hstep := st194_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p71 : ((20373538544587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT194 (i+1))
      = (∑ i ∈ Finset.range 70, stT194 (i+1)) + stT194 71 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 70
    simpa using h
  have hprev := st194_p70
  have hstep := st194_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p72 : ((21356989474933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT194 (i+1))
      = (∑ i ∈ Finset.range 71, stT194 (i+1)) + stT194 72 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 71
    simpa using h
  have hprev := st194_p71
  have hstep := st194_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p73 : ((20194632250317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT194 (i+1))
      = (∑ i ∈ Finset.range 72, stT194 (i+1)) + stT194 73 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 72
    simpa using h
  have hprev := st194_p72
  have hstep := st194_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p74 : ((21272263776981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT194 (i+1))
      = (∑ i ∈ Finset.range 73, stT194 (i+1)) + stT194 74 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 73
    simpa using h
  have hprev := st194_p73
  have hstep := st194_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p75 : ((20574323232747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT194 (i+1))
      = (∑ i ∈ Finset.range 74, stT194 (i+1)) + stT194 75 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 74
    simpa using h
  have hprev := st194_p74
  have hstep := st194_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p76 : ((20662467000423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT194 (i+1))
      = (∑ i ∈ Finset.range 75, stT194 (i+1)) + stT194 76 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 75
    simpa using h
  have hprev := st194_p75
  have hstep := st194_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p77 : ((10618588889579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT194 (i+1))
      = (∑ i ∈ Finset.range 76, stT194 (i+1)) + stT194 77 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 76
    simpa using h
  have hprev := st194_p76
  have hstep := st194_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p78 : ((10097959539233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT194 (i+1))
      = (∑ i ∈ Finset.range 77, stT194 (i+1)) + stT194 78 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 77
    simpa using h
  have hprev := st194_p77
  have hstep := st194_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p79 : ((21281262380191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT194 (i+1))
      = (∑ i ∈ Finset.range 78, stT194 (i+1)) + stT194 79 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 78
    simpa using h
  have hprev := st194_p78
  have hstep := st194_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p80 : ((20647068774031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT194 (i+1))
      = (∑ i ∈ Finset.range 79, stT194 (i+1)) + stT194 80 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 79
    simpa using h
  have hprev := st194_p79
  have hstep := st194_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p81 : ((20504586437823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT194 (i+1))
      = (∑ i ∈ Finset.range 80, stT194 (i+1)) + stT194 81 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 80
    simpa using h
  have hprev := st194_p80
  have hstep := st194_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p82 : ((21362475754203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT194 (i+1))
      = (∑ i ∈ Finset.range 81, stT194 (i+1)) + stT194 82 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 81
    simpa using h
  have hprev := st194_p81
  have hstep := st194_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p83 : ((20271289090329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT194 (i+1))
      = (∑ i ∈ Finset.range 82, stT194 (i+1)) + stT194 83 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 82
    simpa using h
  have hprev := st194_p82
  have hstep := st194_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p84 : ((20925975222999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT194 (i+1))
      = (∑ i ∈ Finset.range 83, stT194 (i+1)) + stT194 84 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 83
    simpa using h
  have hprev := st194_p83
  have hstep := st194_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p85 : ((21143648609619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT194 (i+1))
      = (∑ i ∈ Finset.range 84, stT194 (i+1)) + stT194 85 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 84
    simpa using h
  have hprev := st194_p84
  have hstep := st194_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p86 : ((20195274230211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT194 (i+1))
      = (∑ i ∈ Finset.range 85, stT194 (i+1)) + stT194 86 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 85
    simpa using h
  have hprev := st194_p85
  have hstep := st194_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p87 : ((21181588323187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT194 (i+1))
      = (∑ i ∈ Finset.range 86, stT194 (i+1)) + stT194 87 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 86
    simpa using h
  have hprev := st194_p86
  have hstep := st194_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p88 : ((4184859945951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT194 (i+1))
      = (∑ i ∈ Finset.range 87, stT194 (i+1)) + stT194 88 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 87
    simpa using h
  have hprev := st194_p87
  have hstep := st194_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p89 : ((4047341105421/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT194 (i+1))
      = (∑ i ∈ Finset.range 88, stT194 (i+1)) + stT194 89 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 88
    simpa using h
  have hprev := st194_p88
  have hstep := st194_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p90 : ((21284495111037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT194 (i+1))
      = (∑ i ∈ Finset.range 89, stT194 (i+1)) + stT194 90 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 89
    simpa using h
  have hprev := st194_p89
  have hstep := st194_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p91 : ((5203844534743/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT194 (i+1))
      = (∑ i ∈ Finset.range 90, stT194 (i+1)) + stT194 91 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 90
    simpa using h
  have hprev := st194_p90
  have hstep := st194_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p92 : ((20263793425019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT194 (i+1))
      = (∑ i ∈ Finset.range 91, stT194 (i+1)) + stT194 92 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 91
    simpa using h
  have hprev := st194_p91
  have hstep := st194_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p93 : ((21300196914891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT194 (i+1))
      = (∑ i ∈ Finset.range 92, stT194 (i+1)) + stT194 93 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 92
    simpa using h
  have hprev := st194_p92
  have hstep := st194_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p94 : ((20830110867061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT194 (i+1))
      = (∑ i ∈ Finset.range 93, stT194 (i+1)) + stT194 94 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 93
    simpa using h
  have hprev := st194_p93
  have hstep := st194_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p95 : ((404754027173/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT194 (i+1))
      = (∑ i ∈ Finset.range 94, stT194 (i+1)) + stT194 95 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 94
    simpa using h
  have hprev := st194_p94
  have hstep := st194_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p96 : ((2124605758873/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT194 (i+1))
      = (∑ i ∈ Finset.range 95, stT194 (i+1)) + stT194 96 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 95
    simpa using h
  have hprev := st194_p95
  have hstep := st194_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p97 : ((20960794833733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT194 (i+1))
      = (∑ i ∈ Finset.range 96, stT194 (i+1)) + stT194 97 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 96
    simpa using h
  have hprev := st194_p96
  have hstep := st194_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p98 : ((5047637030117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT194 (i+1))
      = (∑ i ∈ Finset.range 97, stT194 (i+1)) + stT194 98 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 97
    simpa using h
  have hprev := st194_p97
  have hstep := st194_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p99 : ((10543658252303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT194 (i+1))
      = (∑ i ∈ Finset.range 98, stT194 (i+1)) + stT194 99 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 98
    simpa using h
  have hprev := st194_p98
  have hstep := st194_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p100 : ((21176515415407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT194 (i+1))
      = (∑ i ∈ Finset.range 99, stT194 (i+1)) + stT194 100 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 99
    simpa using h
  have hprev := st194_p99
  have hstep := st194_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p101 : ((161740268899/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT194 (i+1))
      = (∑ i ∈ Finset.range 100, stT194 (i+1)) + stT194 101 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 100
    simpa using h
  have hprev := st194_p100
  have hstep := st194_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p102 : ((649541452453/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT194 (i+1))
      = (∑ i ∈ Finset.range 101, stT194 (i+1)) + stT194 102 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 101
    simpa using h
  have hprev := st194_p101
  have hstep := st194_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p103 : ((21372244594649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT194 (i+1))
      = (∑ i ∈ Finset.range 102, stT194 (i+1)) + stT194 103 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 102
    simpa using h
  have hprev := st194_p102
  have hstep := st194_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p104 : ((159734179957/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT194 (i+1))
      = (∑ i ∈ Finset.range 103, stT194 (i+1)) + stT194 104 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 103
    simpa using h
  have hprev := st194_p103
  have hstep := st194_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p105 : ((20398275921319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT194 (i+1))
      = (∑ i ∈ Finset.range 104, stT194 (i+1)) + stT194 105 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 104
    simpa using h
  have hprev := st194_p104
  have hstep := st194_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p106 : ((21346265621879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT194 (i+1))
      = (∑ i ∈ Finset.range 105, stT194 (i+1)) + stT194 106 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 105
    simpa using h
  have hprev := st194_p105
  have hstep := st194_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p107 : ((20908353095619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT194 (i+1))
      = (∑ i ∈ Finset.range 106, stT194 (i+1)) + stT194 107 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 106
    simpa using h
  have hprev := st194_p106
  have hstep := st194_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p108 : ((20174769498757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT194 (i+1))
      = (∑ i ∈ Finset.range 107, stT194 (i+1)) + stT194 108 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 107
    simpa using h
  have hprev := st194_p107
  have hstep := st194_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p109 : ((837497269859/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT194 (i+1))
      = (∑ i ∈ Finset.range 108, stT194 (i+1)) + stT194 109 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 108
    simpa using h
  have hprev := st194_p108
  have hstep := st194_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p110 : ((4270205852029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT194 (i+1))
      = (∑ i ∈ Finset.range 109, stT194 (i+1)) + stT194 110 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 109
    simpa using h
  have hprev := st194_p109
  have hstep := st194_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p111 : ((32695478657/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT194 (i+1))
      = (∑ i ∈ Finset.range 110, stT194 (i+1)) + stT194 111 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 110
    simpa using h
  have hprev := st194_p110
  have hstep := st194_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p112 : ((20345231625441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT194 (i+1))
      = (∑ i ∈ Finset.range 111, stT194 (i+1)) + stT194 112 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 111
    simpa using h
  have hprev := st194_p111
  have hstep := st194_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p113 : ((21284272440241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT194 (i+1))
      = (∑ i ∈ Finset.range 112, stT194 (i+1)) + stT194 113 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 112
    simpa using h
  have hprev := st194_p112
  have hstep := st194_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p114 : ((21100559223169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT194 (i+1))
      = (∑ i ∈ Finset.range 113, stT194 (i+1)) + stT194 114 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 113
    simpa using h
  have hprev := st194_p113
  have hstep := st194_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p115 : ((10107808320347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT194 (i+1))
      = (∑ i ∈ Finset.range 114, stT194 (i+1)) + stT194 115 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 114
    simpa using h
  have hprev := st194_p114
  have hstep := st194_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p116 : ((10301218691669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT194 (i+1))
      = (∑ i ∈ Finset.range 115, stT194 (i+1)) + stT194 116 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 115
    simpa using h
  have hprev := st194_p115
  have hstep := st194_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p117 : ((10701367715419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT194 (i+1))
      = (∑ i ∈ Finset.range 116, stT194 (i+1)) + stT194 117 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 116
    simpa using h
  have hprev := st194_p116
  have hstep := st194_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p118 : ((10439732935819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT194 (i+1))
      = (∑ i ∈ Finset.range 117, stT194 (i+1)) + stT194 118 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 117
    simpa using h
  have hprev := st194_p117
  have hstep := st194_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p119 : ((10080687605091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT194 (i+1))
      = (∑ i ∈ Finset.range 118, stT194 (i+1)) + stT194 119 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 118
    simpa using h
  have hprev := st194_p118
  have hstep := st194_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p120 : ((5191415799933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT194 (i+1))
      = (∑ i ∈ Finset.range 119, stT194 (i+1)) + stT194 120 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 119
    simpa using h
  have hprev := st194_p119
  have hstep := st194_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p121 : ((10711440816711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT194 (i+1))
      = (∑ i ∈ Finset.range 120, stT194 (i+1)) + stT194 121 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 120
    simpa using h
  have hprev := st194_p120
  have hstep := st194_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p122 : ((2078060799321/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT194 (i+1))
      = (∑ i ∈ Finset.range 121, stT194 (i+1)) + stT194 122 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 121
    simpa using h
  have hprev := st194_p121
  have hstep := st194_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p123 : ((62979127133/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT194 (i+1))
      = (∑ i ∈ Finset.range 122, stT194 (i+1)) + stT194 123 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 122
    simpa using h
  have hprev := st194_p122
  have hstep := st194_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p124 : ((5199610701097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT194 (i+1))
      = (∑ i ∈ Finset.range 123, stT194 (i+1)) + stT194 124 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 123
    simpa using h
  have hprev := st194_p123
  have hstep := st194_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p125 : ((21428578253439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT194 (i+1))
      = (∑ i ∈ Finset.range 124, stT194 (i+1)) + stT194 125 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 124
    simpa using h
  have hprev := st194_p124
  have hstep := st194_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p126 : ((10406099876673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT194 (i+1))
      = (∑ i ∈ Finset.range 125, stT194 (i+1)) + stT194 126 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 125
    simpa using h
  have hprev := st194_p125
  have hstep := st194_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p127 : ((4029807942179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT194 (i+1))
      = (∑ i ∈ Finset.range 126, stT194 (i+1)) + stT194 127 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 126
    simpa using h
  have hprev := st194_p126
  have hstep := st194_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p128 : ((10351562817143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT194 (i+1))
      = (∑ i ∈ Finset.range 127, stT194 (i+1)) + stT194 128 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 127
    simpa using h
  have hprev := st194_p127
  have hstep := st194_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p129 : ((5355355129109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT194 (i+1))
      = (∑ i ∈ Finset.range 128, stT194 (i+1)) + stT194 129 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 128
    simpa using h
  have hprev := st194_p128
  have hstep := st194_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p130 : ((10483787906089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT194 (i+1))
      = (∑ i ∈ Finset.range 129, stT194 (i+1)) + stT194 130 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 129
    simpa using h
  have hprev := st194_p129
  have hstep := st194_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p131 : ((20184502852943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT194 (i+1))
      = (∑ i ∈ Finset.range 130, stT194 (i+1)) + stT194 131 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 130
    simpa using h
  have hprev := st194_p130
  have hstep := st194_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p132 : ((20494433223147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT194 (i+1))
      = (∑ i ∈ Finset.range 131, stT194 (i+1)) + stT194 132 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 131
    simpa using h
  have hprev := st194_p131
  have hstep := st194_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p133 : ((10666456442647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT194 (i+1))
      = (∑ i ∈ Finset.range 132, stT194 (i+1)) + stT194 133 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 132
    simpa using h
  have hprev := st194_p132
  have hstep := st194_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p134 : ((4242485642399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT194 (i+1))
      = (∑ i ∈ Finset.range 133, stT194 (i+1)) + stT194 134 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 133
    simpa using h
  have hprev := st194_p133
  have hstep := st194_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p135 : ((20351778982603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT194 (i+1))
      = (∑ i ∈ Finset.range 134, stT194 (i+1)) + stT194 135 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 134
    simpa using h
  have hprev := st194_p134
  have hstep := st194_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p136 : ((2024261926621/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT194 (i+1))
      = (∑ i ∈ Finset.range 135, stT194 (i+1)) + stT194 136 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 135
    simpa using h
  have hprev := st194_p135
  have hstep := st194_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p137 : ((842573422281/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT194 (i+1))
      = (∑ i ∈ Finset.range 136, stT194 (i+1)) + stT194 137 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 136
    simpa using h
  have hprev := st194_p136
  have hstep := st194_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p138 : ((21424581137433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT194 (i+1))
      = (∑ i ∈ Finset.range 137, stT194 (i+1)) + stT194 138 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 137
    simpa using h
  have hprev := st194_p137
  have hstep := st194_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p139 : ((2072790668307/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT194 (i+1))
      = (∑ i ∈ Finset.range 138, stT194 (i+1)) + stT194 139 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 138
    simpa using h
  have hprev := st194_p138
  have hstep := st194_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p140 : ((4025836226563/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT194 (i+1))
      = (∑ i ∈ Finset.range 139, stT194 (i+1)) + stT194 140 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 139
    simpa using h
  have hprev := st194_p139
  have hstep := st194_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p141 : ((10300093461727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT194 (i+1))
      = (∑ i ∈ Finset.range 140, stT194 (i+1)) + stT194 141 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 140
    simpa using h
  have hprev := st194_p140
  have hstep := st194_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p142 : ((21375084141311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT194 (i+1))
      = (∑ i ∈ Finset.range 141, stT194 (i+1)) + stT194 142 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 141
    simpa using h
  have hprev := st194_p141
  have hstep := st194_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p143 : ((2652709106779/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT194 (i+1))
      = (∑ i ∈ Finset.range 142, stT194 (i+1)) + stT194 143 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 142
    simpa using h
  have hprev := st194_p142
  have hstep := st194_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p144 : ((10194395677297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT194 (i+1))
      = (∑ i ∈ Finset.range 143, stT194 (i+1)) + stT194 144 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 143
    simpa using h
  have hprev := st194_p143
  have hstep := st194_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p145 : ((20173121360639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT194 (i+1))
      = (∑ i ∈ Finset.range 144, stT194 (i+1)) + stT194 145 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 144
    simpa using h
  have hprev := st194_p144
  have hstep := st194_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p146 : ((20899326540829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT194 (i+1))
      = (∑ i ∈ Finset.range 145, stT194 (i+1)) + stT194 146 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 145
    simpa using h
  have hprev := st194_p145
  have hstep := st194_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p147 : ((21459488200589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT194 (i+1))
      = (∑ i ∈ Finset.range 146, stT194 (i+1)) + stT194 147 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 146
    simpa using h
  have hprev := st194_p146
  have hstep := st194_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p148 : ((21016858688999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT194 (i+1))
      = (∑ i ∈ Finset.range 147, stT194 (i+1)) + stT194 148 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 147
    simpa using h
  have hprev := st194_p147
  have hstep := st194_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p149 : ((20235198306983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT194 (i+1))
      = (∑ i ∈ Finset.range 148, stT194 (i+1)) + stT194 149 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 148
    simpa using h
  have hprev := st194_p148
  have hstep := st194_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p150 : ((20260501518023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT194 (i+1))
      = (∑ i ∈ Finset.range 149, stT194 (i+1)) + stT194 150 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 149
    simpa using h
  have hprev := st194_p149
  have hstep := st194_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p151 : ((4209761800391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT194 (i+1))
      = (∑ i ∈ Finset.range 150, stT194 (i+1)) + stT194 151 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 150
    simpa using h
  have hprev := st194_p150
  have hstep := st194_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p152 : ((21466454485111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT194 (i+1))
      = (∑ i ∈ Finset.range 151, stT194 (i+1)) + stT194 152 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 151
    simpa using h
  have hprev := st194_p151
  have hstep := st194_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p153 : ((20926572805523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT194 (i+1))
      = (∑ i ∈ Finset.range 152, stT194 (i+1)) + stT194 153 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 152
    simpa using h
  have hprev := st194_p152
  have hstep := st194_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p154 : ((78875553493/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT194 (i+1))
      = (∑ i ∈ Finset.range 153, stT194 (i+1)) + stT194 154 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 153
    simpa using h
  have hprev := st194_p153
  have hstep := st194_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p155 : ((10139779615427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT194 (i+1))
      = (∑ i ∈ Finset.range 154, stT194 (i+1)) + stT194 155 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 154
    simpa using h
  have hprev := st194_p154
  have hstep := st194_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p156 : ((10530939493187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT194 (i+1))
      = (∑ i ∈ Finset.range 155, stT194 (i+1)) + stT194 156 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 155
    simpa using h
  have hprev := st194_p155
  have hstep := st194_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p157 : ((10737884789159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT194 (i+1))
      = (∑ i ∈ Finset.range 156, stT194 (i+1)) + stT194 157 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 156
    simpa using h
  have hprev := st194_p156
  have hstep := st194_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p158 : ((10485748592219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT194 (i+1))
      = (∑ i ∈ Finset.range 157, stT194 (i+1)) + stT194 158 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 157
    simpa using h
  have hprev := st194_p157
  have hstep := st194_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p159 : ((404474267713/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT194 (i+1))
      = (∑ i ∈ Finset.range 158, stT194 (i+1)) + stT194 159 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 158
    simpa using h
  have hprev := st194_p158
  have hstep := st194_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p160 : ((2021194496063/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT194 (i+1))
      = (∑ i ∈ Finset.range 159, stT194 (i+1)) + stT194 160 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 159
    simpa using h
  have hprev := st194_p159
  have hstep := st194_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p161 : ((2094469338557/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT194 (i+1))
      = (∑ i ∈ Finset.range 160, stT194 (i+1)) + stT194 161 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 160
    simpa using h
  have hprev := st194_p160
  have hstep := st194_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p162 : ((10739082230111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT194 (i+1))
      = (∑ i ∈ Finset.range 161, stT194 (i+1)) + stT194 162 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 161
    simpa using h
  have hprev := st194_p161
  have hstep := st194_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p163 : ((5284818514099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT194 (i+1))
      = (∑ i ∈ Finset.range 162, stT194 (i+1)) + stT194 163 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 162
    simpa using h
  have hprev := st194_p162
  have hstep := st194_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p164 : ((20359922284863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT194 (i+1))
      = (∑ i ∈ Finset.range 163, stT194 (i+1)) + stT194 164 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 163
    simpa using h
  have hprev := st194_p163
  have hstep := st194_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p165 : ((10054422339939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT194 (i+1))
      = (∑ i ∈ Finset.range 164, stT194 (i+1)) + stT194 165 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 164
    simpa using h
  have hprev := st194_p164
  have hstep := st194_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p166 : ((5172190750957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT194 (i+1))
      = (∑ i ∈ Finset.range 165, stT194 (i+1)) + stT194 166 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 165
    simpa using h
  have hprev := st194_p165
  have hstep := st194_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p167 : ((21389414074771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT194 (i+1))
      = (∑ i ∈ Finset.range 166, stT194 (i+1)) + stT194 167 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 166
    simpa using h
  have hprev := st194_p166
  have hstep := st194_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p168 : ((21369576829667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT194 (i+1))
      = (∑ i ∈ Finset.range 167, stT194 (i+1)) + stT194 168 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 167
    simpa using h
  have hprev := st194_p167
  have hstep := st194_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p169 : ((10329590231351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT194 (i+1))
      = (∑ i ∈ Finset.range 168, stT194 (i+1)) + stT194 169 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 168
    simpa using h
  have hprev := st194_p168
  have hstep := st194_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p170 : ((10049180157701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT194 (i+1))
      = (∑ i ∈ Finset.range 169, stT194 (i+1)) + stT194 170 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 169
    simpa using h
  have hprev := st194_p169
  have hstep := st194_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p171 : ((1016863767741/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT194 (i+1))
      = (∑ i ∈ Finset.range 170, stT194 (i+1)) + stT194 171 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 170
    simpa using h
  have hprev := st194_p170
  have hstep := st194_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p172 : ((1318379995437/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT194 (i+1))
      = (∑ i ∈ Finset.range 171, stT194 (i+1)) + stT194 172 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 171
    simpa using h
  have hprev := st194_p171
  have hstep := st194_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p173 : ((21503013659657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT194 (i+1))
      = (∑ i ∈ Finset.range 172, stT194 (i+1)) + stT194 173 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 172
    simpa using h
  have hprev := st194_p172
  have hstep := st194_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p174 : ((21106603692557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT194 (i+1))
      = (∑ i ∈ Finset.range 173, stT194 (i+1)) + stT194 174 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 173
    simpa using h
  have hprev := st194_p173
  have hstep := st194_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p175 : ((10176887378693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT194 (i+1))
      = (∑ i ∈ Finset.range 174, stT194 (i+1)) + stT194 175 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 174
    simpa using h
  have hprev := st194_p174
  have hstep := st194_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p176 : ((803127454839/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT194 (i+1))
      = (∑ i ∈ Finset.range 175, stT194 (i+1)) + stT194 176 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 175
    simpa using h
  have hprev := st194_p175
  have hstep := st194_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p177 : ((20576553224939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT194 (i+1))
      = (∑ i ∈ Finset.range 176, stT194 (i+1)) + stT194 177 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 176
    simpa using h
  have hprev := st194_p176
  have hstep := st194_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p178 : ((21303281992857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT194 (i+1))
      = (∑ i ∈ Finset.range 177, stT194 (i+1)) + stT194 178 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 177
    simpa using h
  have hprev := st194_p177
  have hstep := st194_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p179 : ((10739314748211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT194 (i+1))
      = (∑ i ∈ Finset.range 178, stT194 (i+1)) + stT194 179 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 178
    simpa using h
  have hprev := st194_p178
  have hstep := st194_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p180 : ((2092162346691/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT194 (i+1))
      = (∑ i ∈ Finset.range 179, stT194 (i+1)) + stT194 180 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 179
    simpa using h
  have hprev := st194_p179
  have hstep := st194_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p181 : ((1011141328269/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT194 (i+1))
      = (∑ i ∈ Finset.range 180, stT194 (i+1)) + stT194 181 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 180
    simpa using h
  have hprev := st194_p180
  have hstep := st194_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p182 : ((2010907656413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT194 (i+1))
      = (∑ i ∈ Finset.range 181, stT194 (i+1)) + stT194 182 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 181
    simpa using h
  have hprev := st194_p181
  have hstep := st194_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p183 : ((10346103307327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT194 (i+1))
      = (∑ i ∈ Finset.range 182, stT194 (i+1)) + stT194 183 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 182
    simpa using h
  have hprev := st194_p182
  have hstep := st194_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p184 : ((4274497519693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT194 (i+1))
      = (∑ i ∈ Finset.range 183, stT194 (i+1)) + stT194 184 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 183
    simpa using h
  have hprev := st194_p183
  have hstep := st194_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p185 : ((21463283586609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT194 (i+1))
      = (∑ i ∈ Finset.range 184, stT194 (i+1)) + stT194 185 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 184
    simpa using h
  have hprev := st194_p184
  have hstep := st194_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p186 : ((20879016945021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT194 (i+1))
      = (∑ i ∈ Finset.range 185, stT194 (i+1)) + stT194 186 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 185
    simpa using h
  have hprev := st194_p185
  have hstep := st194_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p187 : ((4040600956617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT194 (i+1))
      = (∑ i ∈ Finset.range 186, stT194 (i+1)) + stT194 187 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 186
    simpa using h
  have hprev := st194_p186
  have hstep := st194_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p188 : ((502444134339/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT194 (i+1))
      = (∑ i ∈ Finset.range 187, stT194 (i+1)) + stT194 188 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 187
    simpa using h
  have hprev := st194_p187
  have hstep := st194_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p189 : ((2582551113087/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT194 (i+1))
      = (∑ i ∈ Finset.range 188, stT194 (i+1)) + stT194 189 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 188
    simpa using h
  have hprev := st194_p188
  have hstep := st194_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p190 : ((2668118830859/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT194 (i+1))
      = (∑ i ∈ Finset.range 189, stT194 (i+1)) + stT194 190 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 189
    simpa using h
  have hprev := st194_p189
  have hstep := st194_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p191 : ((10749655705933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT194 (i+1))
      = (∑ i ∈ Finset.range 190, stT194 (i+1)) + stT194 191 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 190
    simpa using h
  have hprev := st194_p190
  have hstep := st194_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p192 : ((2098256692673/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT194 (i+1))
      = (∑ i ∈ Finset.range 191, stT194 (i+1)) + stT194 192 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 191
    simpa using h
  have hprev := st194_p191
  have hstep := st194_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p193 : ((10141250619069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT194 (i+1))
      = (∑ i ∈ Finset.range 192, stT194 (i+1)) + stT194 193 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 192
    simpa using h
  have hprev := st194_p192
  have hstep := st194_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p194 : ((20047647515771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT194 (i+1))
      = (∑ i ∈ Finset.range 193, stT194 (i+1)) + stT194 194 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 193
    simpa using h
  have hprev := st194_p193
  have hstep := st194_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p195 : ((20489066630397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT194 (i+1))
      = (∑ i ∈ Finset.range 194, stT194 (i+1)) + stT194 195 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 194
    simpa using h
  have hprev := st194_p194
  have hstep := st194_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p196 : ((21200690204487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT194 (i+1))
      = (∑ i ∈ Finset.range 195, stT194 (i+1)) + stT194 196 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 195
    simpa using h
  have hprev := st194_p195
  have hstep := st194_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p197 : ((21540817682727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT194 (i+1))
      = (∑ i ∈ Finset.range 196, stT194 (i+1)) + stT194 197 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 196
    simpa using h
  have hprev := st194_p196
  have hstep := st194_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p198 : ((21209751352557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT194 (i+1))
      = (∑ i ∈ Finset.range 197, stT194 (i+1)) + stT194 198 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 197
    simpa using h
  have hprev := st194_p197
  have hstep := st194_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p199 : ((20505034743189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT194 (i+1))
      = (∑ i ∈ Finset.range 198, stT194 (i+1)) + stT194 199 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 198
    simpa using h
  have hprev := st194_p198
  have hstep := st194_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p200 : ((20045535401379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT194 (i+1))
      = (∑ i ∈ Finset.range 199, stT194 (i+1)) + stT194 200 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 199
    simpa using h
  have hprev := st194_p199
  have hstep := st194_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p201 : ((20227034776779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT194 (i+1))
      = (∑ i ∈ Finset.range 200, stT194 (i+1)) + stT194 201 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 200
    simpa using h
  have hprev := st194_p200
  have hstep := st194_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p202 : ((4177696981857/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT194 (i+1))
      = (∑ i ∈ Finset.range 201, stT194 (i+1)) + stT194 202 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 201
    simpa using h
  have hprev := st194_p201
  have hstep := st194_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p203 : ((21463610284221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT194 (i+1))
      = (∑ i ∈ Finset.range 202, stT194 (i+1)) + stT194 203 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 202
    simpa using h
  have hprev := st194_p202
  have hstep := st194_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p204 : ((21468604382841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT194 (i+1))
      = (∑ i ∈ Finset.range 203, stT194 (i+1)) + stT194 204 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 203
    simpa using h
  have hprev := st194_p203
  have hstep := st194_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p205 : ((20903938284823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT194 (i+1))
      = (∑ i ∈ Finset.range 204, stT194 (i+1)) + stT194 205 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 204
    simpa using h
  have hprev := st194_p204
  have hstep := st194_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p206 : ((4048278325747/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT194 (i+1))
      = (∑ i ∈ Finset.range 205, stT194 (i+1)) + stT194 206 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 205
    simpa using h
  have hprev := st194_p205
  have hstep := st194_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p207 : ((20024956150331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT194 (i+1))
      = (∑ i ∈ Finset.range 206, stT194 (i+1)) + stT194 207 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 206
    simpa using h
  have hprev := st194_p206
  have hstep := st194_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p208 : ((20426857101581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT194 (i+1))
      = (∑ i ∈ Finset.range 207, stT194 (i+1)) + stT194 208 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 207
    simpa using h
  have hprev := st194_p207
  have hstep := st194_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p209 : ((21118369121093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT194 (i+1))
      = (∑ i ∈ Finset.range 208, stT194 (i+1)) + stT194 209 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 208
    simpa using h
  have hprev := st194_p208
  have hstep := st194_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p210 : ((21545108077353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT194 (i+1))
      = (∑ i ∈ Finset.range 209, stT194 (i+1)) + stT194 210 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 209
    simpa using h
  have hprev := st194_p209
  have hstep := st194_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p211 : ((10685762762003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT194 (i+1))
      = (∑ i ∈ Finset.range 210, stT194 (i+1)) + stT194 211 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 210
    simpa using h
  have hprev := st194_p210
  have hstep := st194_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p212 : ((20738557577161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT194 (i+1))
      = (∑ i ∈ Finset.range 211, stT194 (i+1)) + stT194 212 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 211
    simpa using h
  have hprev := st194_p211
  have hstep := st194_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p213 : ((20141952551837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT194 (i+1))
      = (∑ i ∈ Finset.range 212, stT194 (i+1)) + stT194 213 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 212
    simpa using h
  have hprev := st194_p212
  have hstep := st194_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p214 : ((20041198811297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT194 (i+1))
      = (∑ i ∈ Finset.range 213, stT194 (i+1)) + stT194 214 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 213
    simpa using h
  have hprev := st194_p213
  have hstep := st194_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p215 : ((4101859397419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT194 (i+1))
      = (∑ i ∈ Finset.range 214, stT194 (i+1)) + stT194 215 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 214
    simpa using h
  have hprev := st194_p214
  have hstep := st194_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p216 : ((2118716184041/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT194 (i+1))
      = (∑ i ∈ Finset.range 215, stT194 (i+1)) + stT194 216 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 215
    simpa using h
  have hprev := st194_p215
  have hstep := st194_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p217 : ((10782049058769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT194 (i+1))
      = (∑ i ∈ Finset.range 216, stT194 (i+1)) + stT194 217 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 216
    simpa using h
  have hprev := st194_p216
  have hstep := st194_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p218 : ((10680916713249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT194 (i+1))
      = (∑ i ∈ Finset.range 217, stT194 (i+1)) + stT194 218 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 217
    simpa using h
  have hprev := st194_p217
  have hstep := st194_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p219 : ((2591773884831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT194 (i+1))
      = (∑ i ∈ Finset.range 218, stT194 (i+1)) + stT194 219 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 218
    simpa using h
  have hprev := st194_p218
  have hstep := st194_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p220 : ((2517978649631/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT194 (i+1))
      = (∑ i ∈ Finset.range 219, stT194 (i+1)) + stT194 220 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 219
    simpa using h
  have hprev := st194_p219
  have hstep := st194_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p221 : ((2502355146533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT194 (i+1))
      = (∑ i ∈ Finset.range 220, stT194 (i+1)) + stT194 221 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 220
    simpa using h
  have hprev := st194_p220
  have hstep := st194_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p222 : ((5111374934889/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT194 (i+1))
      = (∑ i ∈ Finset.range 221, stT194 (i+1)) + stT194 222 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 221
    simpa using h
  have hprev := st194_p221
  have hstep := st194_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p223 : ((4223016488861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT194 (i+1))
      = (∑ i ∈ Finset.range 222, stT194 (i+1)) + stT194 223 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 222
    simpa using h
  have hprev := st194_p222
  have hstep := st194_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p224 : ((5387982056347/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT194 (i+1))
      = (∑ i ∈ Finset.range 223, stT194 (i+1)) + stT194 224 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 223
    simpa using h
  have hprev := st194_p223
  have hstep := st194_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p225 : ((4290259101681/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT194 (i+1))
      = (∑ i ∈ Finset.range 224, stT194 (i+1)) + stT194 225 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 224
    simpa using h
  have hprev := st194_p224
  have hstep := st194_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p226 : ((1305458038653/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT194 (i+1))
      = (∑ i ∈ Finset.range 225, stT194 (i+1)) + stT194 226 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 225
    simpa using h
  have hprev := st194_p225
  have hstep := st194_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p227 : ((5063182040961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT194 (i+1))
      = (∑ i ∈ Finset.range 226, stT194 (i+1)) + stT194 227 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 226
    simpa using h
  have hprev := st194_p226
  have hstep := st194_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p228 : ((19982318587341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT194 (i+1))
      = (∑ i ∈ Finset.range 227, stT194 (i+1)) + stT194 228 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 227
    simpa using h
  have hprev := st194_p227
  have hstep := st194_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p229 : ((20256845513171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT194 (i+1))
      = (∑ i ∈ Finset.range 228, stT194 (i+1)) + stT194 229 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 228
    simpa using h
  have hprev := st194_p228
  have hstep := st194_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p230 : ((20887322909631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT194 (i+1))
      = (∑ i ∈ Finset.range 229, stT194 (i+1)) + stT194 230 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 229
    simpa using h
  have hprev := st194_p229
  have hstep := st194_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p231 : ((10725021369921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT194 (i+1))
      = (∑ i ∈ Finset.range 230, stT194 (i+1)) + stT194 231 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 230
    simpa using h
  have hprev := st194_p230
  have hstep := st194_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p232 : ((10786404157527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT194 (i+1))
      = (∑ i ∈ Finset.range 231, stT194 (i+1)) + stT194 232 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 231
    simpa using h
  have hprev := st194_p231
  have hstep := st194_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p233 : ((10589127924789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT194 (i+1))
      = (∑ i ∈ Finset.range 232, stT194 (i+1)) + stT194 233 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 232
    simpa using h
  have hprev := st194_p232
  have hstep := st194_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p234 : ((10263684691917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT194 (i+1))
      = (∑ i ∈ Finset.range 233, stT194 (i+1)) + stT194 234 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 233
    simpa using h
  have hprev := st194_p233
  have hstep := st194_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p235 : ((20042809617699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT194 (i+1))
      = (∑ i ∈ Finset.range 234, stT194 (i+1)) + stT194 235 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 234
    simpa using h
  have hprev := st194_p234
  have hstep := st194_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p236 : ((20034049199889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT194 (i+1))
      = (∑ i ∈ Finset.range 235, stT194 (i+1)) + stT194 236 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 235
    simpa using h
  have hprev := st194_p235
  have hstep := st194_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p237 : ((5125772983029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT194 (i+1))
      = (∑ i ∈ Finset.range 236, stT194 (i+1)) + stT194 237 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 236
    simpa using h
  have hprev := st194_p236
  have hstep := st194_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p238 : ((10575177518883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT194 (i+1))
      = (∑ i ∈ Finset.range 237, stT194 (i+1)) + stT194 238 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 237
    simpa using h
  have hprev := st194_p237
  have hstep := st194_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p239 : ((10784615257301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT194 (i+1))
      = (∑ i ∈ Finset.range 238, stT194 (i+1)) + stT194 239 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 238
    simpa using h
  have hprev := st194_p238
  have hstep := st194_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p240 : ((10750587830231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT194 (i+1))
      = (∑ i ∈ Finset.range 239, stT194 (i+1)) + stT194 240 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 239
    simpa using h
  have hprev := st194_p239
  have hstep := st194_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p241 : ((20991699650179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT194 (i+1))
      = (∑ i ∈ Finset.range 240, stT194 (i+1)) + stT194 241 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 240
    simpa using h
  have hprev := st194_p240
  have hstep := st194_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p242 : ((20355565172779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT194 (i+1))
      = (∑ i ∈ Finset.range 241, stT194 (i+1)) + stT194 242 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 241
    simpa using h
  have hprev := st194_p241
  have hstep := st194_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p243 : ((19979645586779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT194 (i+1))
      = (∑ i ∈ Finset.range 242, stT194 (i+1)) + stT194 243 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 242
    simpa using h
  have hprev := st194_p242
  have hstep := st194_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p244 : ((20088342428139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT194 (i+1))
      = (∑ i ∈ Finset.range 243, stT194 (i+1)) + stT194 244 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 243
    simpa using h
  have hprev := st194_p243
  have hstep := st194_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p245 : ((4122635301327/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT194 (i+1))
      = (∑ i ∈ Finset.range 244, stT194 (i+1)) + stT194 245 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 244
    simpa using h
  have hprev := st194_p244
  have hstep := st194_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p246 : ((21240010626187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT194 (i+1))
      = (∑ i ∈ Finset.range 245, stT194 (i+1)) + stT194 246 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 245
    simpa using h
  have hprev := st194_p245
  have hstep := st194_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p247 : ((21599370467423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT194 (i+1))
      = (∑ i ∈ Finset.range 246, stT194 (i+1)) + stT194 247 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 246
    simpa using h
  have hprev := st194_p246
  have hstep := st194_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p248 : ((21483398964791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT194 (i+1))
      = (∑ i ∈ Finset.range 247, stT194 (i+1)) + stT194 248 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 247
    simpa using h
  have hprev := st194_p247
  have hstep := st194_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p249 : ((10481335784183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT194 (i+1))
      = (∑ i ∈ Finset.range 248, stT194 (i+1)) + stT194 249 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 248
    simpa using h
  have hprev := st194_p248
  have hstep := st194_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_p250 : ((10169707636671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT194 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT194 (i+1))
      = (∑ i ∈ Finset.range 249, stT194 (i+1)) + stT194 250 := by
    have h := Finset.sum_range_succ (fun i => stT194 (i+1)) 249
    simpa using h
  have hprev := st194_p249
  have hstep := st194_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st194_s250 :
    |Real.sin (((194 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))
      - ((-170229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -3713163/5000000) (δ := 4937/500000000) (ψ := -290733/1000000) 194 171
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 194`** (evaluated boundary). -/
theorem station_194_sign : hardyG ((((194:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 194 250 (by norm_num) (by norm_num)
    ((-290733/1000000 : ℚ) : ℝ)
  have hchain := st194_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT194 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((194 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-290733/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st194_c250
  have hsinb := abs_le.mp st194_s250
  have hbdy_lo : ((4238384912873/301090000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((194 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ))) / 2
          - ((((194:ℕ)):ℝ))
            * Real.sin (((194 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-290733/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((194:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((194:ℝ) * Real.log (250:ℝ) - ((-290733/1000000 : ℚ) : ℝ))) / 2
        - ((194:ℝ)) * Real.sin ((194:ℝ) * Real.log (250:ℝ) - ((-290733/1000000 : ℚ) : ℝ))
        ≥ ((33507403/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((194:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((33507403/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((33507403/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((33507403/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((194:ℕ)):ℝ))+1) * (((((194:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((26318944927/31250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((10169707636671/5000000000000 : ℚ) : ℝ) + ((4238384912873/301090000000000 : ℚ) : ℝ)
      - ((26318944927/31250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-290733/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((194:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-290733/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((194:ℕ)):ℝ)))).re
      - Real.sin ((-290733/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((194:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((194:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((194:ℕ)):ℝ))
      = (((((194:ℕ)):ℝ)) * (Real.log ((((194:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((194:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_194
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
  have hθwin : |(((-290733/1000000 : ℚ) : ℝ) + ((38:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((194:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((194:ℕ)):ℝ)))
    (φ := ((-290733/1000000 : ℚ) : ℝ) + ((38:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-290733/1000000 : ℚ) : ℝ) + ((38:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-290733/1000000 : ℚ)) : ℝ) - Real.pi) + ((38:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-290733/1000000 : ℚ)) : ℝ) - Real.pi) 38).1,
    (cos_sin_shift ((((-290733/1000000 : ℚ)) : ℝ) - Real.pi) 38).2]
  exact cos_sin_flip ((-290733/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_194_sign
end AxiomAudit
