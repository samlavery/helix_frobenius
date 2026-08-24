import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 287` (rung-290.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT287 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((287 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))

theorem st287_c1 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((91923/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58169/312500) (δ := 201/1000000000) (ψ := -744563/1000000) 287 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t1 : ((183821/250000 : ℚ) : ℝ) ≤ stT287 1 := by
  have hc : ((183821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183821/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((183821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c2 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((185579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3460337/10000000) (δ := 3593/250000000) (ψ := -744563/1000000) 287 32
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t2 : ((1311534436093/10000000000000 : ℚ) : ℝ) ≤ stT287 2 := by
  have hc : ((185479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1311534436093/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((185479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c3 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-310973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4717533/10000000) (δ := 14543/1000000000) (ψ := -744563/1000000) 287 50
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t3 : ((-1795980898719/10000000000000 : ℚ) : ℝ) ≤ stT287 3 := by
  have hc : ((-311073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1795980898719/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-311073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c4 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-232971/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3462959/5000000) (δ := 7227/500000000) (ψ := -744563/1000000) 287 63
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t4 : ((-291245058249/625000000000 : ℚ) : ℝ) ≤ stT287 4 := by
  have hc : ((-58249/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291245058249/625000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-58249/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c5 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-668107/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1151229/2000000) (δ := 14433/1000000000) (ψ := -744563/1000000) 287 74
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t5 : ((-373539072519/1250000000000 : ℚ) : ℝ) ≤ stT287 5 := by
  have hc : ((-668207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373539072519/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-668207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c6 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((48547/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24167/400000) (δ := 1439/100000000) (ψ := -744563/1000000) 287 82
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t6 : ((49542960311/125000000000 : ℚ) : ℝ) ≤ stT287 6 := by
  have hc : ((24271/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49542960311/125000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((24271/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c7 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((999851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43209/10000000) (δ := 14463/1000000000) (ψ := -744563/1000000) 287 89
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t7 : ((944675717161/2500000000000 : ℚ) : ℝ) ≤ stT287 7 := by
  have hc : ((999751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((944675717161/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((999751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c8 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((801089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1604209/10000000) (δ := 14419/1000000000) (ψ := -744563/1000000) 287 95
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t8 : ((2831923042137/10000000000000 : ℚ) : ℝ) ≤ stT287 8 := by
  have hc : ((800989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2831923042137/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((800989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c9 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-496861/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1514739/2000000) (δ := 3621/250000000) (ψ := -744563/1000000) 287 100
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t9 : ((-828185165637/2500000000000 : ℚ) : ℝ) ≤ stT287 9 := by
  have hc : ((-496911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-828185165637/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-496911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c10 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-277527/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2315019/5000000) (δ := 2891/200000000) (ψ := -744563/1000000) 287 105
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t10 : ((-438966877153/5000000000000 : ℚ) : ℝ) ≤ stT287 10 := by
  have hc : ((-277627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438966877153/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-277627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c11 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-596463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -552471/1000000) (δ := 14391/1000000000) (ψ := -744563/1000000) 287 110
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t11 : ((-899352726591/5000000000000 : ℚ) : ℝ) ≤ stT287 11 := by
  have hc : ((-596563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899352726591/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-596563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c12 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-89631/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481471/2500000) (δ := 14483/1000000000) (ψ := -744563/1000000) 287 114
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t12 : ((-16173659557/78125000000 : ℚ) : ℝ) ≤ stT287 12 := by
  have hc : ((-179287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16173659557/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-179287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c13 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-90277/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68451/156250) (δ := 7221/500000000) (ψ := -744563/1000000) 287 117
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t13 : ((-250522024827/5000000000000 : ℚ) : ℝ) ≤ stT287 13 := by
  have hc : ((-90327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250522024827/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-90327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c14 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-514653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5278499/10000000) (δ := 1447/100000000) (ψ := -744563/1000000) 287 121
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t14 : ((-1375735559589/10000000000000 : ℚ) : ℝ) ≤ stT287 14 := by
  have hc : ((-514753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1375735559589/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-514753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c15 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((199673/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2899983/10000000) (δ := 3623/250000000) (ψ := -744563/1000000) 287 124
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t15 : ((128856047631/1250000000000 : ℚ) : ℝ) ≤ stT287 15 := by
  have hc : ((199623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128856047631/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((199623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c16 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((83699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3717499/10000000) (δ := 14513/1000000000) (ψ := -744563/1000000) 287 127
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t16 : ((83599/4000000 : ℚ) : ℝ) ≤ stT287 16 := by
  have hc : ((83599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83599/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((83599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c17 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-244801/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7343239/10000000) (δ := 3617/250000000) (ψ := -744563/1000000) 287 130
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t17 : ((-296895226441/1250000000000 : ℚ) : ℝ) ≤ stT287 17 := by
  have hc : ((-122413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296895226441/1250000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-122413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c18 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((620987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2251987/10000000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 132
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t18 : ((731722159257/5000000000000 : ℚ) : ℝ) ≤ stT287 18 := by
  have hc : ((620887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((731722159257/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((620887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c19 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-151657/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6078687/10000000) (δ := 14371/1000000000) (ψ := -744563/1000000) 287 135
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t19 : ((-173985501483/1000000000000 : ℚ) : ℝ) ≤ stT287 19 := by
  have hc : ((-151677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173985501483/1000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-151677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c20 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((961971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -691671/10000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 137
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t20 : ((2150808001357/10000000000000 : ℚ) : ℝ) ≤ stT287 20 := by
  have hc : ((961871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2150808001357/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((961871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c21 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((39957/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2899371/10000000) (δ := 3601/250000000) (ψ := -744563/1000000) 287 139
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t21 : ((43585732283/500000000000 : ℚ) : ℝ) ≤ stT287 21 := by
  have hc : ((39947/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43585732283/500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((39947/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c22 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-45647/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 972309/2000000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 141
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t22 : ((-24336604819/312500000000 : ℚ) : ℝ) ≤ stT287 22 := by
  have hc : ((-91319/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24336604819/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-91319/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c23 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-107103/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1067957/2000000) (δ := 227/15625000) (ψ := -744563/1000000) 287 143
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t23 : ((-44673397567/400000000000 : ℚ) : ℝ) ≤ stT287 23 := by
  have hc : ((-107123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44673397567/400000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-107123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c24 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-211737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4460371/10000000) (δ := 359/25000000) (ψ := -744563/1000000) 287 145
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t24 : ((-216205290777/5000000000000 : ℚ) : ℝ) ≤ stT287 24 := by
  have hc : ((-211837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216205290777/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-211837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c25 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((594871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2334229/10000000) (δ := 7273/500000000) (ψ := -744563/1000000) 287 147
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t25 : ((594771/5000000 : ℚ) : ℝ) ≤ stT287 25 := by
  have hc : ((594771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594771/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((594771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c26 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((930017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188169/2000000) (δ := 451/31250000) (ψ := -744563/1000000) 287 149
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t26 : ((1823716953637/10000000000000 : ℚ) : ℝ) ≤ stT287 26 := by
  have hc : ((929917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1823716953637/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((929917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c27 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-514519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2639053/5000000) (δ := 7193/500000000) (ψ := -744563/1000000) 287 151
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t27 : ((-990384780119/10000000000000 : ℚ) : ℝ) ≤ stT287 27 := by
  have hc : ((-514619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-990384780119/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-514619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c28 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-454941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021551/2000000) (δ := 1451/100000000) (ψ := -744563/1000000) 287 152
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t28 : ((-859946947743/10000000000000 : ℚ) : ℝ) ≤ stT287 28 := by
  have hc : ((-455041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-859946947743/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-455041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c29 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((899547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1130163/10000000) (δ := 14507/1000000000) (ψ := -744563/1000000) 287 154
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t29 : ((1670230804991/10000000000000 : ℚ) : ℝ) ≤ stT287 29 := by
  have hc : ((899447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1670230804991/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((899447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c30 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-494599/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 37431/50000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 155
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t30 : ((-451550727279/2500000000000 : ℚ) : ℝ) ≤ stT287 30 := by
  have hc : ((-494649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451550727279/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-494649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c31 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((987037/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -201487/5000000) (δ := 7237/500000000) (ψ := -744563/1000000) 287 157
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t31 : ((1772591159661/10000000000000 : ℚ) : ℝ) ≤ stT287 31 := by
  have hc : ((986937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1772591159661/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((986937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c32 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-222427/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1333751/2000000) (δ := 14467/1000000000) (ψ := -744563/1000000) 287 158
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t32 : ((-98310826171/625000000000 : ℚ) : ℝ) ≤ stT287 32 := by
  have hc : ((-55613/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98310826171/625000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-55613/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c33 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((482387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -667137/2500000) (δ := 289/20000000) (ψ := -744563/1000000) 287 160
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t33 : ((104944204339/1250000000000 : ℚ) : ℝ) ≤ stT287 33 := by
  have hc : ((482287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104944204339/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((482287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c34 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((86567/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 380377/1250000) (δ := 14357/1000000000) (ψ := -744563/1000000) 287 161
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t34 : ((14841823187/250000000000 : ℚ) : ℝ) ≤ stT287 34 := by
  have hc : ((43271/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14841823187/250000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((43271/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c35 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-124219/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7574379/10000000) (δ := 1809/125000000) (ψ := -744563/1000000) 287 163
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t35 : ((-419979245067/2500000000000 : ℚ) : ℝ) ≤ stT287 35 := by
  have hc : ((-248463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419979245067/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-248463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c36 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((336227/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1534861/5000000) (δ := 1803/125000000) (ψ := -744563/1000000) 287 164
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t36 : ((280105721291/5000000000000 : ℚ) : ℝ) ≤ stT287 36 := by
  have hc : ((336127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280105721291/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((336127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c37 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((469267/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881097/10000000) (δ := 14517/1000000000) (ψ := -744563/1000000) 287 165
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t37 : ((771387586613/5000000000000 : ℚ) : ℝ) ≤ stT287 37 := by
  have hc : ((469217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771387586613/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((469217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c38 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-37911/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269223/625000) (δ := 14493/1000000000) (ψ := -744563/1000000) 287 166
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t38 : ((-769254353/31250000000 : ℚ) : ℝ) ≤ stT287 38 := by
  have hc : ((-2371/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-769254353/31250000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-2371/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c39 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-969703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3618513/5000000) (δ := 29/2000000) (ψ := -744563/1000000) 287 167
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t39 : ((-776464043723/5000000000000 : ℚ) : ℝ) ≤ stT287 39 := by
  have hc : ((-969803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-776464043723/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-969803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c40 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-370499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6013379/10000000) (δ := 2903/200000000) (ψ := -744563/1000000) 287 169
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t40 : ((-585889475311/5000000000000 : ℚ) : ℝ) ≤ stT287 40 := by
  have hc : ((-370549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-585889475311/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-370549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c41 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-387/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2002201/5000000) (δ := 7211/500000000) (ψ := -744563/1000000) 287 170
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t41 : ((-1212689557/250000000000 : ℚ) : ℝ) ≤ stT287 41 := by
  have hc : ((-1553/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1212689557/250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-1553/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c42 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((283089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2422337/10000000) (δ := 14529/1000000000) (ψ := -744563/1000000) 287 171
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t42 : ((436738517287/5000000000000 : ℚ) : ℝ) ≤ stT287 42 := by
  have hc : ((283039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436738517287/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((283039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c43 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((281/320 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1247167/10000000) (δ := 14367/1000000000) (ψ := -744563/1000000) 287 172
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t43 : ((10711799637/80000000000 : ℚ) : ℝ) ≤ stT287 43 := by
  have hc : ((35121/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10711799637/80000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((35121/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c44 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((245777/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115041/2500000) (δ := 14359/1000000000) (ψ := -744563/1000000) 287 173
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t44 : ((11577653191/78125000000 : ℚ) : ℝ) ≤ stT287 44 := by
  have hc : ((30719/31250 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11577653191/78125000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((30719/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c45 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((499923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43893/10000000) (δ := 14451/1000000000) (ψ := -744563/1000000) 287 174
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t45 : ((745166179703/5000000000000 : ℚ) : ℝ) ≤ stT287 45 := by
  have hc : ((499873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((745166179703/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((499873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c46 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((499987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4501/2500000) (δ := 2889/200000000) (ψ := -744563/1000000) 287 175
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t46 : ((737116611603/5000000000000 : ℚ) : ℝ) ≤ stT287 46 := by
  have hc : ((499937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((737116611603/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((499937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c47 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((99463/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -259189/10000000) (δ := 7219/500000000) (ψ := -744563/1000000) 287 176
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t47 : ((145067018997/1000000000000 : ℚ) : ℝ) ≤ stT287 47 := by
  have hc : ((99453/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145067018997/1000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((99453/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c48 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((941233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430669/5000000) (δ := 14531/1000000000) (ψ := -744563/1000000) 287 177
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t48 : ((10867262751/80000000000 : ℚ) : ℝ) ≤ stT287 48 := by
  have hc : ((941133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10867262751/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((941133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c49 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((151671/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71001/400000) (δ := 1803/125000000) (ψ := -744563/1000000) 287 178
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t49 : ((216644220721/2000000000000 : ℚ) : ℝ) ≤ stT287 49 := by
  have hc : ((151651/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216644220721/2000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((151651/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c50 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((367021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2987479/10000000) (δ := 14387/1000000000) (ψ := -744563/1000000) 287 179
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t50 : ((518904448173/10000000000000 : ℚ) : ℝ) ≤ stT287 50 := by
  have hc : ((366921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518904448173/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((366921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c51 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-44433/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4487077/10000000) (δ := 14409/1000000000) (ψ := -744563/1000000) 287 180
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t51 : ((-62246691293/2000000000000 : ℚ) : ℝ) ≤ stT287 51 := by
  have hc : ((-44453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62246691293/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-44453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c52 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-804139/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6262553/10000000) (δ := 14501/1000000000) (ψ := -744563/1000000) 287 181
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t52 : ((-1115279237489/10000000000000 : ℚ) : ℝ) ≤ stT287 52 := by
  have hc : ((-804239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1115279237489/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-804239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c53 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-983883/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 740453/1000000) (δ := 7201/500000000) (ψ := -744563/1000000) 287 181
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t53 : ((-675802476349/5000000000000 : ℚ) : ℝ) ≤ stT287 53 := by
  have hc : ((-983983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675802476349/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-983983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c54 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-455081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5108149/10000000) (δ := 3627/250000000) (ψ := -744563/1000000) 287 182
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t54 : ((-154855762467/2500000000000 : ℚ) : ℝ) ≤ stT287 54 := by
  have hc : ((-455181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154855762467/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-455181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c55 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((8094/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513133/2000000) (δ := 2903/200000000) (ψ := -744563/1000000) 287 183
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t55 : ((174589354121/2500000000000 : ℚ) : ℝ) ≤ stT287 55 := by
  have hc : ((129479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174589354121/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((129479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c56 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((498169/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8561/400000) (δ := 719/50000000) (ψ := -744563/1000000) 287 184
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t56 : ((332819704207/2500000000000 : ℚ) : ℝ) ≤ stT287 56 := by
  have hc : ((498119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332819704207/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((498119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c57 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((34759/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128901/400000) (δ := 1443/100000000) (ψ := -744563/1000000) 287 185
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t57 : ((23011425569/625000000000 : ℚ) : ℝ) ≤ stT287 57 := by
  have hc : ((69493/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23011425569/625000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((69493/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c58 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-846807/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -201621/312500) (δ := 7183/500000000) (ψ := -744563/1000000) 287 186
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t58 : ((-222408787991/2000000000000 : ℚ) : ℝ) ≤ stT287 58 := by
  have hc : ((-846907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222408787991/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-846907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c59 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-684959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72667/125000) (δ := 7183/500000000) (ψ := -744563/1000000) 287 186
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t59 : ((-89187146151/1000000000000 : ℚ) : ℝ) ≤ stT287 59 := by
  have hc : ((-685059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89187146151/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-685059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c60 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((324017/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2164491/10000000) (δ := 14359/1000000000) (ψ := -744563/1000000) 287 187
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t60 : ((209119726599/2500000000000 : ℚ) : ℝ) ≤ stT287 60 := by
  have hc : ((323967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209119726599/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((323967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c61 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((97707/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1683699/10000000) (δ := 14551/1000000000) (ψ := -744563/1000000) 287 188
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t61 : ((15635613947/156250000000 : ℚ) : ℝ) ≤ stT287 61 := by
  have hc : ((195389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15635613947/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((195389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c62 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-82339/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2862377/5000000) (δ := 7179/500000000) (ψ := -744563/1000000) 287 189
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t62 : ((-104586569703/1250000000000 : ℚ) : ℝ) ≤ stT287 62 := by
  have hc : ((-164703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104586569703/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-164703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c63 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-26717/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5755533/10000000) (δ := 7179/500000000) (ψ := -744563/1000000) 287 189
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t63 : ((-16832653461/200000000000 : ℚ) : ℝ) ≤ stT287 63 := by
  have hc : ((-26721/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16832653461/200000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-26721/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c64 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((85833/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53879/400000) (δ := 7183/500000000) (ψ := -744563/1000000) 287 190
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t64 : ((85823/800000 : ℚ) : ℝ) ≤ stT287 64 := by
  have hc : ((85823/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85823/800000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((85823/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c65 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((68153/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -129469/400000) (δ := 1443/100000000) (ψ := -744563/1000000) 287 191
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t65 : ((2640698763/78125000000 : ℚ) : ℝ) ≤ stT287 65 := by
  have hc : ((4258/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2640698763/78125000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((4258/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c66 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-199703/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3858853/5000000) (δ := 1453/100000000) (ψ := -744563/1000000) 287 191
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t66 : ((-49168407309/400000000000 : ℚ) : ℝ) ≤ stT287 66 := by
  have hc : ((-199723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49168407309/400000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-199723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c67 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((87177/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699859/2500000) (δ := 14523/1000000000) (ψ := -744563/1000000) 287 192
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t67 : ((53239591979/1000000000000 : ℚ) : ℝ) ≤ stT287 67 := by
  have hc : ((87157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53239591979/1000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((87157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c68 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((612579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2278693/10000000) (δ := 3629/250000000) (ψ := -744563/1000000) 287 193
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t68 : ((371369904381/5000000000000 : ℚ) : ℝ) ≤ stT287 68 := by
  have hc : ((612479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371369904381/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((612479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c69 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-990659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7512017/10000000) (δ := 14409/1000000000) (ψ := -744563/1000000) 287 194
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t69 : ((-1192734138981/10000000000000 : ℚ) : ℝ) ≤ stT287 69 := by
  have hc : ((-990759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1192734138981/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-990759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c70 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((215701/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4499/16000) (δ := 14509/1000000000) (ψ := -744563/1000000) 287 194
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t70 : ((64438028357/1250000000000 : ℚ) : ℝ) ≤ stT287 70 := by
  have hc : ((215651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64438028357/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((215651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c71 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((464741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2718637/10000000) (δ := 7251/500000000) (ψ := -744563/1000000) 287 195
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t71 : ((551427110621/10000000000000 : ℚ) : ℝ) ≤ stT287 71 := by
  have hc : ((464641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((551427110621/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((464641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c72 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-976981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7316533/10000000) (δ := 7201/500000000) (ψ := -744563/1000000) 287 195
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t72 : ((-71968855217/625000000000 : ℚ) : ℝ) ≤ stT287 72 := by
  have hc : ((-977081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71968855217/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-977081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c73 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((164829/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 752631/5000000) (δ := 7247/500000000) (ψ := -744563/1000000) 287 196
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t73 : ((192894266499/2000000000000 : ℚ) : ℝ) ≤ stT287 73 := by
  have hc : ((164809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192894266499/2000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((164809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c74 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-102017/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4440683/10000000) (δ := 14387/1000000000) (ψ := -744563/1000000) 287 197
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t74 : ((-118650539959/5000000000000 : ℚ) : ℝ) ≤ stT287 74 := by
  have hc : ((-102067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118650539959/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-102067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c75 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-484123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5190391/10000000) (δ := 14487/1000000000) (ψ := -744563/1000000) 287 197
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t75 : ((-559132782323/10000000000000 : ℚ) : ℝ) ≤ stT287 75 := by
  have hc : ((-484223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-559132782323/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-484223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c76 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((229711/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1014141/10000000) (δ := 719/50000000) (ψ := -744563/1000000) 287 198
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t76 : ((65866939377/625000000000 : ℚ) : ℝ) ≤ stT287 76 := by
  have hc : ((114843/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65866939377/625000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((114843/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c77 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-489587/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -917859/1250000) (δ := 1453/100000000) (ψ := -744563/1000000) 287 199
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t77 : ((-278996631511/2500000000000 : ℚ) : ℝ) ≤ stT287 77 := by
  have hc : ((-489637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278996631511/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-489637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c78 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((360301/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1915317/10000000) (δ := 14373/1000000000) (ψ := -744563/1000000) 287 199
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t78 : ((407903921527/5000000000000 : ℚ) : ℝ) ≤ stT287 78 := by
  have hc : ((360251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407903921527/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((360251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c79 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-143057/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2326207/5000000) (δ := 7233/500000000) (ψ := -744563/1000000) 287 200
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t79 : ((-5031499013/156250000000 : ℚ) : ℝ) ≤ stT287 79 := by
  have hc : ((-143107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5031499013/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-143107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c80 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-17741/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34983/80000) (δ := 7233/500000000) (ψ := -744563/1000000) 287 200
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t80 : ((-9923110767/500000000000 : ℚ) : ℝ) ≤ stT287 80 := by
  have hc : ((-17751/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9923110767/500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-17751/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c81 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((566307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302743/1250000) (δ := 2889/200000000) (ψ := -744563/1000000) 287 201
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t81 : ((629118825977/10000000000000 : ℚ) : ℝ) ≤ stT287 81 := by
  have hc : ((566207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((629118825977/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((566207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c82 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-831579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6381853/10000000) (δ := 2909/200000000) (ψ := -744563/1000000) 287 201
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t82 : ((-229609106641/2500000000000 : ℚ) : ℝ) ≤ stT287 82 := by
  have hc : ((-831679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229609106641/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-831679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c83 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((193703/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314503/5000000) (δ := 3613/250000000) (ψ := -744563/1000000) 287 202
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t83 : ((106297297743/1000000000000 : ℚ) : ℝ) ≤ stT287 83 := by
  have hc : ((193683/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106297297743/1000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((193683/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c84 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-499517/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3872041/5000000) (δ := 3593/125000000) (ψ := -744563/1000000) 287 203
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t84 : ((-54507255803/500000000000 : ℚ) : ℝ) ≤ stT287 84 := by
  have hc : ((-499567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54507255803/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-499567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c85 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((477837/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5837/78125) (δ := 14359/1000000000) (ψ := -744563/1000000) 287 203
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t85 : ((129558156281/1250000000000 : ℚ) : ℝ) ≤ stT287 85 := by
  have hc : ((477787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129558156281/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((477787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c86 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-435389/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6568947/10000000) (δ := 7233/500000000) (ψ := -744563/1000000) 287 204
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t86 : ((-58693258249/625000000000 : ℚ) : ℝ) ≤ stT287 86 := by
  have hc : ((-435439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58693258249/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-435439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c87 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((48187/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862999/5000000) (δ := 14537/1000000000) (ψ := -744563/1000000) 287 204
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t87 : ((12913790061/156250000000 : ℚ) : ℝ) ≤ stT287 87 := by
  have hc : ((192723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12913790061/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((192723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c88 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-675729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5781873/10000000) (δ := 1453/100000000) (ψ := -744563/1000000) 287 205
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t88 : ((-180109104329/2500000000000 : ℚ) : ℝ) ≤ stT287 88 := by
  have hc : ((-675829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180109104329/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-675829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c89 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((149417/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2325519/10000000) (δ := 14473/1000000000) (ψ := -744563/1000000) 287 205
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t89 : ((9897191989/156250000000 : ℚ) : ℝ) ≤ stT287 89 := by
  have hc : ((9337/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9897191989/156250000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((9337/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c90 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-34013/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2682801/5000000) (δ := 14423/1000000000) (ψ := -744563/1000000) 287 206
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t90 : ((-143437813161/2500000000000 : ℚ) : ℝ) ≤ stT287 90 := by
  have hc : ((-136077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143437813161/2500000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-136077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c91 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((259521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1281333/5000000) (δ := 361/12500000) (ψ := -744563/1000000) 287 206
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t91 : ((67999824441/1250000000000 : ℚ) : ℝ) ≤ stT287 91 := by
  have hc : ((259471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67999824441/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((259471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c92 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-523271/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -662963/1250000) (δ := 1811/125000000) (ψ := -744563/1000000) 287 207
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t92 : ((-545652473583/10000000000000 : ℚ) : ℝ) ≤ stT287 92 := by
  have hc : ((-523371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-545652473583/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-523371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c93 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((555987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 613279/2500000) (δ := 2903/200000000) (ψ := -744563/1000000) 287 207
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t93 : ((576427580537/10000000000000 : ℚ) : ℝ) ≤ stT287 93 := by
  have hc : ((555887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((576427580537/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((555887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c94 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-614373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5580969/10000000) (δ := 2879/200000000) (ψ := -744563/1000000) 287 208
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t94 : ((-316890485303/5000000000000 : ℚ) : ℝ) ≤ stT287 94 := by
  have hc : ((-614473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316890485303/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-614473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c95 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((138669/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251461/1250000) (δ := 2899/200000000) (ψ := -744563/1000000) 287 208
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t95 : ((71125411861/1000000000000 : ℚ) : ℝ) ≤ stT287 95 := by
  have hc : ((138649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71125411861/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((138649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c96 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-49053/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3091559/5000000) (δ := 14401/1000000000) (ψ := -744563/1000000) 287 209
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t96 : ((-200283603177/2500000000000 : ℚ) : ℝ) ≤ stT287 96 := by
  have hc : ((-196237/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200283603177/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-196237/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c97 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((438581/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252191/10000000) (δ := 14401/1000000000) (ψ := -744563/1000000) 287 209
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t97 : ((222630348363/2500000000000 : ℚ) : ℝ) ≤ stT287 97 := by
  have hc : ((438531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222630348363/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((438531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c98 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-238619/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7096733/10000000) (δ := 14509/1000000000) (ψ := -744563/1000000) 287 210
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t98 : ((-60266738133/625000000000 : ℚ) : ℝ) ≤ stT287 98 := by
  have hc : ((-59661/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60266738133/625000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-59661/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c99 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((199437/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93807/5000000) (δ := 14509/1000000000) (ψ := -744563/1000000) 287 210
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t99 : ((200421463429/2000000000000 : ℚ) : ℝ) ≤ stT287 99 := by
  have hc : ((199417/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200421463429/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((199417/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c100 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-122933/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 462419/625000) (δ := 14409/1000000000) (ψ := -744563/1000000) 287 210
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t100 : ((-245891/2500000 : ℚ) : ℝ) ≤ stT287 100 := by
  have hc : ((-245891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245891/2500000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-245891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c101 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((357/400 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1169847/10000000) (δ := 3629/250000000) (ψ := -744563/1000000) 287 211
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t101 : ((2219927547/25000000000 : ℚ) : ℝ) ≤ stT287 101 := by
  have hc : ((2231/2500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2219927547/25000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((2231/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c102 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-709561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2949589/5000000) (δ := 901/62500000) (ψ := -744563/1000000) 287 211
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t102 : ((-175667354957/2500000000000 : ℚ) : ℝ) ≤ stT287 102 := by
  have hc : ((-709661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175667354957/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-709661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c103 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((432517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175549/625000) (δ := 14479/1000000000) (ψ := -744563/1000000) 287 212
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t103 : ((426073010193/10000000000000 : ℚ) : ℝ) ≤ stT287 103 := by
  have hc : ((432417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426073010193/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((432417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c104 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-3143/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412363/1000000) (δ := 3631/250000000) (ψ := -744563/1000000) 287 212
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t104 : ((-3085888407/400000000000 : ℚ) : ℝ) ≤ stT287 104 := by
  have hc : ((-3147/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3085888407/400000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-3147/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c105 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-311233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4718217/10000000) (δ := 14531/1000000000) (ψ := -744563/1000000) 287 213
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t105 : ((-303830186033/10000000000000 : ℚ) : ℝ) ≤ stT287 105 := by
  have hc : ((-311333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303830186033/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-311333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c106 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((134517/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8331/40000) (δ := 14431/1000000000) (ψ := -744563/1000000) 287 213
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t106 : ((26126983729/400000000000 : ℚ) : ℝ) ≤ stT287 106 := by
  have hc : ((134497/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26126983729/400000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((134497/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c107 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-926279/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215251/312500) (δ := 2873/200000000) (ψ := -744563/1000000) 287 214
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t107 : ((-895564855323/10000000000000 : ℚ) : ℝ) ≤ stT287 107 := by
  have hc : ((-926379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-895564855323/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-926379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c108 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((498177/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5339/250000) (δ := 2873/200000000) (ψ := -744563/1000000) 287 214
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t108 : ((1917290823/20000000000 : ℚ) : ℝ) ≤ stT287 108 := by
  have hc : ((498127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1917290823/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((498127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c109 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-417723/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6399351/10000000) (δ := 7269/500000000) (ψ := -744563/1000000) 287 214
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t109 : ((-400154259271/5000000000000 : ℚ) : ℝ) ≤ stT287 109 := by
  have hc : ((-417773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400154259271/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-417773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c110 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((5643/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689011/2500000) (δ := 7179/500000000) (ψ := -744563/1000000) 287 215
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t110 : ((10758388477/250000000000 : ℚ) : ℝ) ≤ stT287 110 := by
  have hc : ((22567/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10758388477/250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((22567/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c111 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((3791/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3737259/10000000) (δ := 7229/500000000) (ψ := -744563/1000000) 287 215
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t111 : ((1796754201/250000000000 : ℚ) : ℝ) ≤ stT287 111 := by
  have hc : ((1893/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1796754201/250000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((1893/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c112 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-599997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2767867/5000000) (δ := 14551/1000000000) (ψ := -744563/1000000) 287 216
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t112 : ((-35439928529/625000000000 : ℚ) : ℝ) ≤ stT287 112 := by
  have hc : ((-600097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35439928529/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-600097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c113 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((943801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210531/2500000) (δ := 897/62500000) (ψ := -744563/1000000) 287 216
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t113 : ((11096980059/125000000000 : ℚ) : ℝ) ≤ stT287 113 := by
  have hc : ((943701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11096980059/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((943701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c114 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-481063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7163729/10000000) (δ := 14551/1000000000) (ψ := -744563/1000000) 287 216
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t114 : ((-225301850109/2500000000000 : ℚ) : ℝ) ≤ stT287 114 := by
  have hc : ((-481113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225301850109/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-481113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c115 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((30643/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569451/2500000) (δ := 14359/1000000000) (ψ := -744563/1000000) 287 217
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t115 : ((1785628597/31250000000 : ℚ) : ℝ) ≤ stT287 115 := by
  have hc : ((15319/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1785628597/31250000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((15319/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c116 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-183/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3934311/10000000) (δ := 14359/1000000000) (ψ := -744563/1000000) 287 217
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t116 : ((-702857089/2500000000000 : ℚ) : ℝ) ≤ stT287 116 := by
  have hc : ((-757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-702857089/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c117 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-312493/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701847/1250000) (δ := 3609/250000000) (ψ := -744563/1000000) 287 218
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t117 : ((-288946316043/5000000000000 : ℚ) : ℝ) ≤ stT287 117 := by
  have hc : ((-312543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288946316043/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-312543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c118 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((39229/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 491651/10000000) (δ := 1817/125000000) (ψ := -744563/1000000) 287 218
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t118 : ((722190303/8000000000 : ℚ) : ℝ) ≤ stT287 118 := by
  have hc : ((1569/1600 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((722190303/8000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((1569/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c119 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-433163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654649/1000000) (δ := 1817/125000000) (ψ := -744563/1000000) 287 218
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t119 : ((-397125923887/5000000000000 : ℚ) : ℝ) ≤ stT287 119 := by
  have hc : ((-433213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397125923887/5000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-433213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c120 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((303067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1578609/5000000) (δ := 14529/1000000000) (ψ := -744563/1000000) 287 219
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t120 : ((27656948529/1000000000000 : ℚ) : ℝ) ≤ stT287 120 := by
  have hc : ((302967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27656948529/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((302967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c121 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((436701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2797171/10000000) (δ := 14529/1000000000) (ψ := -744563/1000000) 287 219
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t121 : ((39690960309/1000000000000 : ℚ) : ℝ) ≤ stT287 121 := by
  have hc : ((436601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39690960309/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((436601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c122 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-188589/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218919/312500) (δ := 14381/1000000000) (ψ := -744563/1000000) 287 220
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t122 : ((-85379333511/1000000000000 : ℚ) : ℝ) ≤ stT287 122 := by
  have hc : ((-188609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85379333511/1000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-188609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c123 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((179273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14353/125000) (δ := 14481/1000000000) (ψ := -744563/1000000) 287 220
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t123 : ((161626873257/2000000000000 : ℚ) : ℝ) ≤ stT287 123 := by
  have hc : ((179253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161626873257/2000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((179253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c124 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-57919/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4661501/10000000) (δ := 14481/1000000000) (ψ := -744563/1000000) 287 220
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t124 : ((-52030786353/2000000000000 : ℚ) : ℝ) ≤ stT287 124 := by
  have hc : ((-57939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52030786353/2000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-57939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c125 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-516319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5283359/10000000) (δ := 3597/250000000) (ψ := -744563/1000000) 287 221
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t125 : ((-115474903333/2500000000000 : ℚ) : ℝ) ≤ stT287 125 := by
  have hc : ((-516419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115474903333/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-516419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c126 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((984981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13557/312500) (δ := 2903/200000000) (ψ := -744563/1000000) 287 221
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t126 : ((87740093647/1000000000000 : ℚ) : ℝ) ≤ stT287 126 := by
  have hc : ((984881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87740093647/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((984881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c127 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-382647/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3052867/5000000) (δ := 1811/125000000) (ψ := -744563/1000000) 287 221
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t127 : ((-339588861829/5000000000000 : ℚ) : ℝ) ≤ stT287 127 := by
  have hc : ((-382697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339588861829/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-382697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c128 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-2387/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1987367/5000000) (δ := 3627/250000000) (ψ := -744563/1000000) 287 222
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t128 : ((-1060439829/625000000000 : ℚ) : ℝ) ≤ stT287 128 := by
  have hc : ((-4799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1060439829/625000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-4799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c129 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((399971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321799/2000000) (δ := 2879/200000000) (ψ := -744563/1000000) 287 222
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t129 : ((7042208889/100000000000 : ℚ) : ℝ) ≤ stT287 129 := by
  have hc : ((399921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7042208889/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((399921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c130 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-480281/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714953/1000000) (δ := 2879/200000000) (ψ := -744563/1000000) 287 222
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t130 : ((-421278626529/5000000000000 : ℚ) : ℝ) ≤ stT287 130 := by
  have hc : ((-480331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421278626529/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-480331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c131 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((339773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3060303/10000000) (δ := 29/2000000) (ψ := -744563/1000000) 287 223
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t131 : ((37096707349/1250000000000 : ℚ) : ℝ) ≤ stT287 131 := by
  have hc : ((339673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37096707349/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((339673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c132 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((574831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1197999/5000000) (δ := 14403/1000000000) (ψ := -744563/1000000) 287 223
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t132 : ((125059741407/2500000000000 : ℚ) : ℝ) ≤ stT287 132 := by
  have hc : ((574731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125059741407/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((574731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c133 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-999853/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3905557/5000000) (δ := 14403/1000000000) (ψ := -744563/1000000) 287 223
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t133 : ((-86706924583/1000000000000 : ℚ) : ℝ) ≤ stT287 133 := by
  have hc : ((-999953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86706924583/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-999953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c134 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((133193/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -630577/2500000) (δ := 2871/100000000) (ψ := -744563/1000000) 287 224
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t134 : ((1797493341/39062500000 : ℚ) : ℝ) ≤ stT287 134 := by
  have hc : ((8323/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1797493341/39062500000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((8323/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c135 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((21563/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2812269/10000000) (δ := 1451/100000000) (ψ := -744563/1000000) 287 224
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t135 : ((4638537849/125000000000 : ℚ) : ℝ) ≤ stT287 135 := by
  have hc : ((10779/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4638537849/125000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((10779/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c136 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-994863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7600473/10000000) (δ := 7193/500000000) (ψ := -744563/1000000) 287 225
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t136 : ((-853173807759/10000000000000 : ℚ) : ℝ) ≤ stT287 136 := by
  have hc : ((-994963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-853173807759/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-994963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c137 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((295863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -585999/2500000) (δ := 14417/1000000000) (ψ := -744563/1000000) 287 225
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t137 : ((252729907241/5000000000000 : ℚ) : ℝ) ≤ stT287 137 := by
  have hc : ((295813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252729907241/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((295813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c138 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((51099/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1437083/5000000) (δ := 7193/500000000) (ψ := -744563/1000000) 287 225
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t138 : ((10871922411/312500000000 : ℚ) : ℝ) ≤ stT287 138 := by
  have hc : ((102173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10871922411/312500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((102173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c139 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-498389/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478327/625000) (δ := 14379/1000000000) (ψ := -744563/1000000) 287 226
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t139 : ((-422770476971/5000000000000 : ℚ) : ℝ) ≤ stT287 139 := by
  have hc : ((-498439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422770476971/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-498439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c140 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((134247/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2509833/10000000) (δ := 1803/125000000) (ψ := -744563/1000000) 287 226
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t140 : ((28359565047/625000000000 : ℚ) : ℝ) ≤ stT287 140 := by
  have hc : ((67111/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28359565047/625000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((67111/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c141 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((507289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2596901/10000000) (δ := 14479/1000000000) (ψ := -744563/1000000) 287 226
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t141 : ((427129723539/10000000000000 : ℚ) : ℝ) ≤ stT287 141 := by
  have hc : ((507189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((427129723539/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((507189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c142 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-997223/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7667617/10000000) (δ := 14479/1000000000) (ψ := -744563/1000000) 287 226
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t142 : ((-418467754893/5000000000000 : ℚ) : ℝ) ≤ stT287 142 := by
  have hc : ((-997323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418467754893/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-997323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c143 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((90103/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502609/5000000) (δ := 3593/250000000) (ψ := -744563/1000000) 287 227
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t143 : ((18831751719/625000000000 : ℚ) : ℝ) ≤ stT287 143 := by
  have hc : ((45039/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18831751719/625000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((45039/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c144 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((698211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1994753/10000000) (δ := 14531/1000000000) (ψ := -744563/1000000) 287 227
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t144 : ((581758933963/10000000000000 : ℚ) : ℝ) ≤ stT287 144 := by
  have hc : ((698111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581758933963/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((698111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c145 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-234193/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6960211/10000000) (δ := 1809/125000000) (ψ := -744563/1000000) 287 227
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t145 : ((-19450750919/250000000000 : ℚ) : ℝ) ≤ stT287 145 := by
  have hc : ((-117109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19450750919/250000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-117109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c146 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((11051/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1908223/5000000) (δ := 7219/500000000) (ψ := -744563/1000000) 287 228
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t146 : ((912517273/250000000000 : ℚ) : ℝ) ≤ stT287 146 := by
  have hc : ((5513/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((912517273/250000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((5513/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c147 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((45397/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1081137/10000000) (δ := 2873/200000000) (ψ := -744563/1000000) 287 228
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t147 : ((1169958941/15625000000 : ℚ) : ℝ) ≤ stT287 147 := by
  have hc : ((2837/3125 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1169958941/15625000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((2837/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c148 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-361257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1486393/2500000) (δ := 7219/500000000) (ψ := -744563/1000000) 287 228
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t148 : ((-59398509493/1000000000000 : ℚ) : ℝ) ≤ stT287 148 := by
  have hc : ((-361307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59398509493/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-361307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c149 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-15631/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197227/400000) (δ := 14457/1000000000) (ψ := -744563/1000000) 287 229
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t149 : ((-80054327/2500000000 : ℚ) : ℝ) ≤ stT287 149 := by
  have hc : ((-3127/8000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80054327/2500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-3127/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c150 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((998619/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131389/10000000) (δ := 14357/1000000000) (ψ := -744563/1000000) 287 229
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t150 : ((50955423089/625000000000 : ℚ) : ℝ) ≤ stT287 150 := by
  have hc : ((998519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50955423089/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((998519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c151 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-13993/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289757/625000) (δ := 7273/500000000) (ψ := -744563/1000000) 287 229
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t151 : ((-5695709211/250000000000 : ℚ) : ℝ) ≤ stT287 151 := by
  have hc : ((-6999/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5695709211/250000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-6999/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c152 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-821219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126717/200000) (δ := 291/20000000) (ψ := -744563/1000000) 287 230
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t152 : ((-166544602863/2500000000000 : ℚ) : ℝ) ≤ stT287 152 := by
  have hc : ((-821319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166544602863/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-821319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c153 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((15893/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326183/2000000) (δ := 14353/1000000000) (ψ := -744563/1000000) 287 230
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t153 : ((3211777683/50000000000 : ℚ) : ℝ) ≤ stT287 153 := by
  have hc : ((15891/20000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3211777683/50000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((15891/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c154 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((346131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1521691/5000000) (δ := 289/20000000) (ψ := -744563/1000000) 287 230
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t154 : ((139419696241/5000000000000 : ℚ) : ℝ) ≤ stT287 154 := by
  have hc : ((346031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139419696241/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((346031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c155 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-997781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7687401/10000000) (δ := 14353/1000000000) (ψ := -744563/1000000) 287 230
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t155 : ((-40075898841/500000000000 : ℚ) : ℝ) ≤ stT287 155 := by
  have hc : ((-997881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40075898841/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-997881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c156 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((103369/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -425799/1250000) (δ := 14543/1000000000) (ψ := -744563/1000000) 287 231
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t156 : ((129252069/7812500000 : ℚ) : ℝ) ≤ stT287 156 := by
  have hc : ((103319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129252069/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((103319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c157 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((222743/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117829/1000000) (δ := 359/25000000) (ψ := -744563/1000000) 287 231
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t157 : ((44437029437/625000000000 : ℚ) : ℝ) ≤ stT287 157 := by
  have hc : ((111359/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44437029437/625000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((111359/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c158 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-330721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5733841/10000000) (δ := 359/25000000) (ψ := -744563/1000000) 287 231
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t158 : ((-131573757609/2500000000000 : ℚ) : ℝ) ≤ stT287 158 := by
  have hc : ((-330771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131573757609/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-330771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c159 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-571319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5447271/10000000) (δ := 14467/1000000000) (ψ := -744563/1000000) 287 232
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t159 : ((-113291245197/2500000000000 : ℚ) : ℝ) ≤ stT287 159 := by
  have hc : ((-571419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113291245197/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-571419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c160 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((464419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -948833/10000000) (δ := 14467/1000000000) (ψ := -744563/1000000) 287 232
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t160 : ((367115735961/5000000000000 : ℚ) : ℝ) ≤ stT287 160 := by
  have hc : ((464369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367115735961/5000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((464369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c161 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((80733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70431/200000) (δ := 1817/125000000) (ψ := -744563/1000000) 287 232
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t161 : ((6358707913/500000000000 : ℚ) : ℝ) ≤ stT287 161 := by
  have hc : ((80683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6358707913/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((80683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c162 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-499513/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7743653/10000000) (δ := 14429/1000000000) (ψ := -744563/1000000) 287 233
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t162 : ((-15699766401/200000000000 : ℚ) : ℝ) ≤ stT287 162 := by
  have hc : ((-499563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15699766401/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-499563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c163 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((237221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332823/1000000) (δ := 14529/1000000000) (ψ := -744563/1000000) 287 233
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t163 : ((9286369723/500000000000 : ℚ) : ℝ) ≤ stT287 163 := by
  have hc : ((237121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9286369723/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((237121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c164 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((911427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66259/625000) (δ := 7187/500000000) (ψ := -744563/1000000) 287 233
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t164 : ((177906522959/2500000000000 : ℚ) : ℝ) ≤ stT287 164 := by
  have hc : ((911327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177906522959/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((911327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c165 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-70367/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2710913/5000000) (δ := 14529/1000000000) (ψ := -744563/1000000) 287 233
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t165 : ((-109580740741/2500000000000 : ℚ) : ℝ) ≤ stT287 165 := by
  have hc : ((-140759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109580740741/2500000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-140759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c166 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-144791/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5950787/10000000) (δ := 14521/1000000000) (ψ := -744563/1000000) 287 234
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t166 : ((-112395202461/2000000000000 : ℚ) : ℝ) ≤ stT287 166 := by
  have hc : ((-144811/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112395202461/2000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-144811/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c167 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((396047/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164141/1000000) (δ := 14421/1000000000) (ψ := -744563/1000000) 287 234
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t167 : ((306431586531/5000000000000 : ℚ) : ℝ) ≤ stT287 167 := by
  have hc : ((395997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306431586531/5000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((395997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c168 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((491613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2642137/10000000) (δ := 7191/500000000) (ψ := -744563/1000000) 287 234
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t168 : ((94802535927/2500000000000 : ℚ) : ℝ) ≤ stT287 168 := by
  have hc : ((491513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94802535927/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((491513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c169 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-464063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1725089/2500000) (δ := 7191/500000000) (ψ := -744563/1000000) 287 234
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t169 : ((-357010107103/5000000000000 : ℚ) : ℝ) ≤ stT287 169 := by
  have hc : ((-464113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-357010107103/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-464113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c170 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-128073/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4574573/10000000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 235
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t170 : ((-19653171339/1000000000000 : ℚ) : ℝ) ≤ stT287 170 := by
  have hc : ((-128123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19653171339/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-128123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c171 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((989281/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -366363/10000000) (δ := 14489/1000000000) (ψ := -744563/1000000) 287 235
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t171 : ((756445505139/10000000000000 : ℚ) : ℝ) ≤ stT287 171 := by
  have hc : ((989181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((756445505139/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((989181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c172 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((43859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3817307/10000000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 235
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t172 : ((8341471857/2500000000000 : ℚ) : ℝ) ≤ stT287 172 := by
  have hc : ((43759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8341471857/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((43759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c173 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-199759/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7731237/10000000) (δ := 14507/1000000000) (ψ := -744563/1000000) 287 236
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t173 : ((-75944588397/1000000000000 : ℚ) : ℝ) ≤ stT287 173 := by
  have hc : ((-199779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75944588397/1000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-199779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c174 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((2064/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1797891/5000000) (δ := 14407/1000000000) (ψ := -744563/1000000) 287 236
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t174 : ((12508237951/1250000000000 : ℚ) : ℝ) ≤ stT287 174 := by
  have hc : ((32999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12508237951/1250000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((32999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c175 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((39151/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103199/2000000) (δ := 14507/1000000000) (ψ := -744563/1000000) 287 236
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t175 : ((3699039177/50000000000 : ℚ) : ℝ) ≤ stT287 175 := by
  have hc : ((39147/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3699039177/50000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((39147/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c176 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-2141/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 460431/1000000) (δ := 14507/1000000000) (ψ := -744563/1000000) 287 236
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t176 : ((-8072219311/400000000000 : ℚ) : ℝ) ≤ stT287 176 := by
  have hc : ((-10709/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8072219311/400000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-10709/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c177 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-473631/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7038441/10000000) (δ := 14503/1000000000) (ψ := -744563/1000000) 287 237
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t177 : ((-356040902607/5000000000000 : ℚ) : ℝ) ≤ stT287 177 := by
  have hc : ((-473681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356040902607/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-473681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c178 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((181889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -299619/1000000) (δ := 9/625000) (ψ := -744563/1000000) 287 237
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t178 : ((136293967509/5000000000000 : ℚ) : ℝ) ≤ stT287 178 := by
  have hc : ((181839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136293967509/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((181839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c179 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((458683/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51173/500000) (δ := 29/2000000) (ψ := -744563/1000000) 287 237
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t179 : ((68559671271/1000000000000 : ℚ) : ℝ) ≤ stT287 179 := by
  have hc : ((458633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68559671271/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((458633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c180 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-105911/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5020653/10000000) (δ := 14403/1000000000) (ψ := -744563/1000000) 287 237
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t180 : ((-1233750519/39062500000 : ℚ) : ℝ) ≤ stT287 180 := by
  have hc : ((-6621/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1233750519/39062500000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-6621/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c181 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-89751/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6712217/10000000) (δ := 14393/1000000000) (ψ := -744563/1000000) 287 238
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t181 : ((-13343780499/200000000000 : ℚ) : ℝ) ≤ stT287 181 := by
  have hc : ((-89761/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13343780499/200000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-89761/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c182 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((450357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2759079/10000000) (δ := 14393/1000000000) (ψ := -744563/1000000) 287 238
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t182 : ((333752550993/10000000000000 : ℚ) : ℝ) ≤ stT287 182 := by
  have hc : ((450257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333752550993/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((450257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c183 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((223007/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 586231/5000000) (δ := 14493/1000000000) (ψ := -744563/1000000) 287 238
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t183 : ((82416488511/1250000000000 : ℚ) : ℝ) ≤ stT287 183 := by
  have hc : ((111491/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82416488511/1250000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((111491/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c184 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-22297/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101651/200000) (δ := 14493/1000000000) (ψ := -744563/1000000) 287 238
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t184 : ((-822062871/25000000000 : ℚ) : ℝ) ≤ stT287 184 := by
  have hc : ((-11151/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-822062871/25000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-11151/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c185 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-3607/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6736491/10000000) (δ := 14417/1000000000) (ψ := -744563/1000000) 287 239
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t185 : ((-2652214591/40000000000 : ℚ) : ℝ) ≤ stT287 185 := by
  have hc : ((-18037/20000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2652214591/40000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-18037/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c186 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((205413/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179287/625000) (δ := 14417/1000000000) (ψ := -744563/1000000) 287 239
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t186 : ((30115867861/1000000000000 : ℚ) : ℝ) ≤ stT287 186 := by
  have hc : ((205363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30115867861/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((205363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c187 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((462177/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978643/10000000) (δ := 14417/1000000000) (ψ := -744563/1000000) 287 239
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t187 : ((42242566943/625000000000 : ℚ) : ℝ) ≤ stT287 187 := by
  have hc : ((462127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42242566943/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((462127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c188 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-43017/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2402643/5000000) (δ := 14517/1000000000) (ψ := -744563/1000000) 287 239
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t188 : ((-2510599207/100000000000 : ℚ) : ℝ) ≤ stT287 188 := by
  have hc : ((-86059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2510599207/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-86059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c189 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-47721/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774067/2500000) (δ := 581/40000000) (ψ := -744563/1000000) 287 240
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t189 : ((-17357779159/250000000000 : ℚ) : ℝ) ≤ stT287 189 := by
  have hc : ((-23863/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17357779159/250000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-23863/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c190 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((24429/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3310021/10000000) (δ := 7189/500000000) (ψ := -744563/1000000) 287 240
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t190 : ((4428849611/250000000000 : ℚ) : ℝ) ≤ stT287 190 := by
  have hc : ((24419/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4428849611/250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((24419/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c191 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((49169/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57053/1250000) (δ := 581/40000000) (ψ := -744563/1000000) 287 240
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t191 : ((4446724017/62500000000 : ℚ) : ℝ) ≤ stT287 191 := by
  have hc : ((12291/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4446724017/62500000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((12291/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c192 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-55117/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4203137/10000000) (δ := 577/40000000) (ψ := -744563/1000000) 287 240
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t192 : ((-4976670237/625000000000 : ℚ) : ℝ) ≤ stT287 192 := by
  have hc : ((-55167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4976670237/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-55167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c193 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-999533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7777557/10000000) (δ := 3633/250000000) (ψ := -744563/1000000) 287 241
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t193 : ((-89943978441/1250000000000 : ℚ) : ℝ) ≤ stT287 193 := by
  have hc : ((-999633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89943978441/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-999633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c194 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-2849/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4069517/10000000) (δ := 3633/250000000) (ψ := -744563/1000000) 287 241
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t194 : ((-1024527493/250000000000 : ℚ) : ℝ) ≤ stT287 194 := by
  have hc : ((-1427/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1024527493/250000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-1427/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c195 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((247109/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -380563/10000000) (δ := 14371/1000000000) (ψ := -744563/1000000) 287 241
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t195 : ((22117538947/312500000000 : ℚ) : ℝ) ≤ stT287 195 := by
  have hc : ((61771/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22117538947/312500000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((61771/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c196 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((126117/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3289521/10000000) (δ := 14471/1000000000) (ψ := -744563/1000000) 287 241
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t196 : ((18009553419/1000000000000 : ℚ) : ℝ) ≤ stT287 196 := by
  have hc : ((126067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18009553419/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((126067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c197 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-29189/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6940951/10000000) (δ := 3633/250000000) (ψ := -744563/1000000) 287 241
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t197 : ((-166388339927/2500000000000 : ℚ) : ℝ) ≤ stT287 197 := by
  have hc : ((-233537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166388339927/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-233537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c198 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-232149/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1026819/2000000) (δ := 3591/250000000) (ψ := -744563/1000000) 287 242
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t198 : ((-16501686333/500000000000 : ℚ) : ℝ) ≤ stT287 198 := by
  have hc : ((-232199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16501686333/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-232199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c199 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((820913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1519473/10000000) (δ := 14539/1000000000) (ψ := -744563/1000000) 287 242
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t199 : ((581858740253/10000000000000 : ℚ) : ℝ) ≤ stT287 199 := by
  have hc : ((820813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581858740253/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((820813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c200 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((674287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 415399/2000000) (δ := 113/7812500) (ψ := -744563/1000000) 287 242
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t200 : ((238360836411/5000000000000 : ℚ) : ℝ) ≤ stT287 200 := by
  have hc : ((674187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238360836411/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((674187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c201 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-637649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2827799/5000000) (δ := 113/7812500) (ψ := -744563/1000000) 287 242
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t201 : ((-224916853077/5000000000000 : ℚ) : ℝ) ≤ stT287 201 := by
  have hc : ((-637749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224916853077/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-637749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c202 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-427579/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1622907/2500000) (δ := 14457/1000000000) (ψ := -744563/1000000) 287 243
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t202 : ((-150439454571/2500000000000 : ℚ) : ℝ) ≤ stT287 202 := by
  have hc : ((-427629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150439454571/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-427629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c203 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((190759/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2948397/10000000) (δ := 7273/500000000) (ψ := -744563/1000000) 287 243
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t203 : ((66925700079/2500000000000 : ℚ) : ℝ) ≤ stT287 203 := by
  have hc : ((190709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66925700079/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((190709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c204 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((973447/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288699/5000000) (δ := 7273/500000000) (ψ := -744563/1000000) 287 243
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t204 : ((34073958429/500000000000 : ℚ) : ℝ) ≤ stT287 204 := by
  have hc : ((973347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34073958429/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((973347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c205 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-1271/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4085973/10000000) (δ := 7273/500000000) (ψ := -744563/1000000) 287 243
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t205 : ((-889102663/200000000000 : ℚ) : ℝ) ≤ stT287 205 := by
  have hc : ((-1273/20000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-889102663/200000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-1273/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c206 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-99389/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7577471/10000000) (δ := 14357/1000000000) (ψ := -744563/1000000) 287 243
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t206 : ((-34627331433/500000000000 : ℚ) : ℝ) ≤ stT287 206 := by
  have hc : ((-99399/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34627331433/500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-99399/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c207 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-287461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4655927/10000000) (δ := 289/20000000) (ψ := -744563/1000000) 287 244
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t207 : ((-199868985489/10000000000000 : ℚ) : ℝ) ≤ stT287 207 := by
  have hc : ((-287561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199868985489/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-287561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c208 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((887349/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1198079/10000000) (δ := 14353/1000000000) (ψ := -744563/1000000) 287 244
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t208 : ((4921570203/80000000000 : ℚ) : ℝ) ≤ stT287 208 := by
  have hc : ((887249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4921570203/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((887249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c209 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((31187/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1121597/5000000) (δ := 291/20000000) (ψ := -744563/1000000) 287 244
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t209 : ((5392256487/125000000000 : ℚ) : ℝ) ≤ stT287 209 := by
  have hc : ((15591/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5392256487/125000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((15591/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c210 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-320737/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5668037/10000000) (δ := 289/20000000) (ψ := -744563/1000000) 287 244
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t210 : ((-110682100971/2500000000000 : ℚ) : ℝ) ≤ stT287 210 := by
  have hc : ((-320787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110682100971/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-320787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c211 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-441391/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6631371/10000000) (δ := 14543/1000000000) (ψ := -744563/1000000) 287 245
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t211 : ((-303900786189/5000000000000 : ℚ) : ℝ) ≤ stT287 211 := by
  have hc : ((-441441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303900786189/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-441441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c212 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((33969/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3238959/10000000) (δ := 14443/1000000000) (ψ := -744563/1000000) 287 245
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t212 : ((23321392113/1250000000000 : ℚ) : ℝ) ≤ stT287 212 := by
  have hc : ((67913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23321392113/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((67913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c213 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((998487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34381/2500000) (δ := 14543/1000000000) (ψ := -744563/1000000) 287 245
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t213 : ((171020697939/2500000000000 : ℚ) : ℝ) ≤ stT287 213 := by
  have hc : ((998387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171020697939/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((998387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c214 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((42667/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3498223/10000000) (δ := 723/50000000) (ψ := -744563/1000000) 287 245
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t214 : ((2914943157/250000000000 : ℚ) : ℝ) ≤ stT287 214 := by
  have hc : ((21321/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2914943157/250000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((21321/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c215 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-459687/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 855401/1250000) (δ := 723/50000000) (ψ := -744563/1000000) 287 245
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t215 : ((-62707667063/1000000000000 : ℚ) : ℝ) ≤ stT287 215 := by
  have hc : ((-459737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62707667063/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-459737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c216 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-74981/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5535269/10000000) (δ := 2907/200000000) (ψ := -744563/1000000) 287 246
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t216 : ((-51026627309/1250000000000 : ℚ) : ℝ) ≤ stT287 216 := by
  have hc : ((-149987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51026627309/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-149987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c217 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((63059/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277651/1250000) (δ := 2887/200000000) (ψ := -744563/1000000) 287 246
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t217 : ((10700108839/250000000000 : ℚ) : ℝ) ≤ stT287 217 := by
  have hc : ((63049/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10700108839/250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((63049/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c218 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((36341/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 538821/5000000) (δ := 449/31250000) (ψ := -744563/1000000) 287 246
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t218 : ((4922101009/80000000000 : ℚ) : ℝ) ≤ stT287 218 := by
  have hc : ((36337/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4922101009/80000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((36337/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c219 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-1729/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272589/625000) (δ := 2887/200000000) (ψ := -744563/1000000) 287 246
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t219 : ((-58451337/5000000000 : ℚ) : ℝ) ≤ stT287 219 := by
  have hc : ((-173/1000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58451337/5000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-173/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c220 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-995997/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7630211/10000000) (δ := 3617/250000000) (ψ := -744563/1000000) 287 246
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t220 : ((-3357842987/50000000000 : ℚ) : ℝ) ≤ stT287 220 := by
  have hc : ((-996097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3357842987/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-996097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c221 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-17553/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4823747/10000000) (δ := 227/15625000) (ψ := -744563/1000000) 287 247
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t221 : ((-5905396267/250000000000 : ℚ) : ℝ) ≤ stT287 221 := by
  have hc : ((-8779/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5905396267/250000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-8779/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c222 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((402889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1584521/10000000) (δ := 23/1600000) (ψ := -744563/1000000) 287 247
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t222 : ((67591952971/1250000000000 : ℚ) : ℝ) ≤ stT287 222 := by
  have hc : ((402839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67591952971/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((402839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c223 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((792387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1640211/10000000) (δ := 23/1600000) (ψ := -744563/1000000) 287 247
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t223 : ((530554197263/10000000000000 : ℚ) : ℝ) ≤ stT287 223 := by
  have hc : ((792287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530554197263/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((792287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c224 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-361067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4850521/10000000) (δ := 3607/250000000) (ψ := -744563/1000000) 287 247
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t224 : ((-120657587859/5000000000000 : ℚ) : ℝ) ≤ stT287 224 := by
  have hc : ((-361167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120657587859/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-361167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c225 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-199407/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766141/1000000) (δ := 7191/500000000) (ψ := -744563/1000000) 287 248
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t225 : ((-132951399809/2000000000000 : ℚ) : ℝ) ≤ stT287 225 := by
  have hc : ((-199427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132951399809/2000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-199427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c226 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-27407/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223981/500000) (δ := 14441/500000000) (ψ := -744563/1000000) 287 248
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t226 : ((-36478409249/2500000000000 : ℚ) : ℝ) ≤ stT287 226 := by
  have hc : ((-54839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36478409249/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-54839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c227 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((43273/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655911/5000000) (δ := 7191/500000000) (ψ := -744563/1000000) 287 248
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t227 : ((7179491691/125000000000 : ℚ) : ℝ) ≤ stT287 227 := by
  have hc : ((10817/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7179491691/125000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((10817/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c228 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((740617/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1842021/10000000) (δ := 7191/500000000) (ψ := -744563/1000000) 287 248
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t228 : ((245209615761/5000000000000 : ℚ) : ℝ) ≤ stT287 228 := by
  have hc : ((740517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245209615761/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((740517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c229 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-409621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622761/1250000) (δ := 7191/500000000) (ψ := -744563/1000000) 287 248
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t229 : ((-270751421499/10000000000000 : ℚ) : ℝ) ≤ stT287 229 := by
  have hc : ((-409721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270751421499/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-409721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c230 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-124353/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7599513/10000000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 249
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t230 : ((-164008495511/2500000000000 : ℚ) : ℝ) ≤ stT287 230 := by
  have hc : ((-248731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164008495511/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-248731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c231 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-111011/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4486711/10000000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 249
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t231 : ((-2283525221/156250000000 : ℚ) : ℝ) ≤ stT287 231 := by
  have hc : ((-111061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2283525221/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-111061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c232 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((424961/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -693699/5000000) (δ := 7257/500000000) (ψ := -744563/1000000) 287 249
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t232 : ((69741917163/1250000000000 : ℚ) : ℝ) ≤ stT287 232 := by
  have hc : ((424911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69741917163/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((424911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c233 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((388957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849321/5000000) (δ := 14489/1000000000) (ψ := -744563/1000000) 287 249
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t233 : ((254781142747/5000000000000 : ℚ) : ℝ) ≤ stT287 233 := by
  have hc : ((388907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254781142747/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((388907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c234 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-20713/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4771479/10000000) (δ := 14389/1000000000) (ψ := -744563/1000000) 287 249
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t234 : ((-54178435317/2500000000000 : ℚ) : ℝ) ≤ stT287 234 := by
  have hc : ((-82877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54178435317/2500000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-82877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c235 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-499979/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3915593/5000000) (δ := 14389/1000000000) (ψ := -744563/1000000) 287 249
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t235 : ((-326183417541/5000000000000 : ℚ) : ℝ) ≤ stT287 235 := by
  have hc : ((-500029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326183417541/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-500029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c236 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-176711/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4830057/10000000) (δ := 3599/250000000) (ψ := -744563/1000000) 287 250
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t236 : ((-23012337829/1000000000000 : ℚ) : ℝ) ≤ stT287 236 := by
  have hc : ((-176761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23012337829/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-176761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c237 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((752793/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449063/2500000) (δ := 14407/1000000000) (ψ := -744563/1000000) 287 250
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t237 : ((488926039317/10000000000000 : ℚ) : ℝ) ≤ stT287 237 := by
  have hc : ((752693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488926039317/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((752693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c238 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((441187/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 612391/5000000) (δ := 3599/250000000) (ψ := -744563/1000000) 287 250
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t238 : ((285946326811/5000000000000 : ℚ) : ℝ) ≤ stT287 238 := by
  have hc : ((441137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285946326811/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((441137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c239 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-122173/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1058297/2500000) (δ := 453/31250000) (ψ := -744563/1000000) 287 250
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t239 : ((-79091923231/10000000000000 : ℚ) : ℝ) ≤ stT287 239 := by
  have hc : ((-122273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79091923231/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-122273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c240 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-484459/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7229037/10000000) (δ := 14407/1000000000) (ψ := -744563/1000000) 287 250
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t240 : ((-156374795241/2500000000000 : ℚ) : ℝ) ≤ stT287 240 := by
  have hc : ((-484509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156374795241/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-484509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c241 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-117413/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5495561/10000000) (δ := 3601/250000000) (ψ := -744563/1000000) 287 251
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t241 : ((-75645288981/2000000000000 : ℚ) : ℝ) ≤ stT287 241 := by
  have hc : ((-117433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75645288981/2000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-117433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c242 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((266009/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2524537/10000000) (δ := 3601/250000000) (ψ := -744563/1000000) 287 251
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t242 : ((21370603527/625000000000 : ℚ) : ℝ) ≤ stT287 242 := by
  have hc : ((265959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21370603527/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((265959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c243 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((492477/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217109/5000000) (δ := 1813/125000000) (ψ := -744563/1000000) 287 251
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t243 : ((631783841/10000000000 : ℚ) : ℝ) ≤ stT287 243 := by
  have hc : ((492427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((631783841/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((492427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c244 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((54181/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3380847/10000000) (δ := 1813/125000000) (ψ := -744563/1000000) 287 251
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t244 : ((1083431397/78125000000 : ℚ) : ℝ) ≤ stT287 244 := by
  have hc : ((13539/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1083431397/78125000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((13539/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c245 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-816521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3157693/5000000) (δ := 7201/250000000) (ψ := -744563/1000000) 287 251
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t245 : ((-521720374617/10000000000000 : ℚ) : ℝ) ≤ stT287 245 := by
  have hc : ((-816621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521720374617/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-816621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c246 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-85063/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6469949/10000000) (δ := 1799/125000000) (ψ := -744563/1000000) 287 252
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t246 : ((-54240588121/1000000000000 : ℚ) : ℝ) ≤ stT287 246 := by
  have hc : ((-85073/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54240588121/1000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-85073/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c247 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((36647/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711839/2000000) (δ := 1799/125000000) (ψ := -744563/1000000) 287 252
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t247 : ((2912749081/312500000000 : ℚ) : ℝ) ≤ stT287 247 := by
  have hc : ((18311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2912749081/312500000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((18311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c248 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((241333/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41263/625000) (δ := 1799/125000000) (ψ := -744563/1000000) 287 252
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t248 : ((7661529/125000000 : ℚ) : ℝ) ≤ stT287 248 := by
  have hc : ((60327/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7661529/125000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((60327/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c249 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((157191/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 556771/2500000) (δ := 14411/1000000000) (ψ := -744563/1000000) 287 252
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t249 : ((12449983273/312500000000 : ℚ) : ℝ) ≤ stT287 249 := by
  have hc : ((78583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12449983273/312500000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((78583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c250 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-453209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318931/625000) (δ := 14511/1000000000) (ψ := -744563/1000000) 287 252
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t250 : ((-35837249613/1250000000000 : ℚ) : ℝ) ≤ stT287 250 := by
  have hc : ((-453309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35837249613/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-453309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c251 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-15609/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -967601/1250000) (δ := 2897/200000000) (ψ := -744563/1000000) 287 253
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t251 : ((-31530588791/500000000000 : ℚ) : ℝ) ≤ stT287 251 := by
  have hc : ((-249769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31530588791/500000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-249769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c252 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-37499/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1221989/2500000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 253
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t252 : ((-23628456969/1000000000000 : ℚ) : ℝ) ≤ stT287 252 := by
  have hc : ((-37509/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23628456969/1000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-37509/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c253 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((341641/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2046369/10000000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 253
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t253 : ((107378106077/2500000000000 : ℚ) : ℝ) ≤ stT287 253 := by
  have hc : ((341591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107378106077/2500000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((341591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c254 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((475613/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31361/400000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 253
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t254 : ((59678876433/1000000000000 : ℚ) : ℝ) ≤ stT287 254 := by
  have hc : ((475563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59678876433/1000000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((475563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c255 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((32279/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1801649/5000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 253
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t255 : ((631194653/78125000000 : ℚ) : ℝ) ≤ stT287 255 := by
  have hc : ((16127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((631194653/78125000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((16127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c256 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-26191/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6411521/10000000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 253
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t256 : ((-130970834553/2500000000000 : ℚ) : ℝ) ≤ stT287 256 := by
  have hc : ((-209553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130970834553/2500000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-209553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c257 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-856723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6499197/10000000) (δ := 7239/500000000) (ψ := -744563/1000000) 287 254
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t257 : ((-534471621409/10000000000000 : ℚ) : ℝ) ≤ stT287 257 := by
  have hc : ((-856823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534471621409/10000000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-856823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c258 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((42789/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -742557/2000000) (δ := 581/40000000) (ψ := -744563/1000000) 287 254
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t258 : ((6652026177/1250000000000 : ℚ) : ℝ) ≤ stT287 258 := by
  have hc : ((42739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6652026177/1250000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((42739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c259 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((930561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -937137/10000000) (δ := 7239/500000000) (ψ := -744563/1000000) 287 254
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t259 : ((578159621109/10000000000000 : ℚ) : ℝ) ≤ stT287 259 := by
  have hc : ((930461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((578159621109/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((930461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c260 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((744421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1827821/10000000) (δ := 7239/500000000) (ψ := -744563/1000000) 287 254
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t260 : ((461607787533/10000000000000 : ℚ) : ℝ) ≤ stT287 260 := by
  have hc : ((744321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461607787533/10000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((744321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c261 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-129539/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57277/125000) (δ := 7239/500000000) (ψ := -744563/1000000) 287 254
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t261 : ((-16042729433/1000000000000 : ℚ) : ℝ) ≤ stT287 261 := by
  have hc : ((-129589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16042729433/1000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-129589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c262 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-488889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57234/78125) (δ := 21539/500000000) (ψ := -744563/1000000) 287 254
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t262 : ((-302067981017/5000000000000 : ℚ) : ℝ) ≤ stT287 262 := by
  have hc : ((-488939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302067981017/5000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-488939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c263 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-1986/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1129739/2000000) (δ := 14371/1000000000) (ψ := -744563/1000000) 287 255
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t263 : ((-19597022687/500000000000 : ℚ) : ℝ) ≤ stT287 263 := by
  have hc : ((-31781/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19597022687/500000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-31781/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c264 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((38989/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2925711/10000000) (δ := 43171/1000000000) (ψ := -744563/1000000) 287 255
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t264 : ((23989898403/1000000000000 : ℚ) : ℝ) ≤ stT287 264 := by
  have hc : ((38979/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23989898403/1000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((38979/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c265 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((996371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106529/5000000) (δ := 3633/250000000) (ψ := -744563/1000000) 287 255
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t265 : ((122400858789/2000000000000 : ℚ) : ℝ) ≤ stT287 265 := by
  have hc : ((996271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122400858789/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((996271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c266 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((67983/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 497881/2000000) (δ := 14471/1000000000) (ψ := -744563/1000000) 287 255
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t266 : ((83350728799/2500000000000 : ℚ) : ℝ) ≤ stT287 266 := by
  have hc : ((135941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83350728799/2500000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((135941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c267 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-481071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5181681/10000000) (δ := 3633/250000000) (ψ := -744563/1000000) 287 255
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t267 : ((-294472321461/10000000000000 : ℚ) : ℝ) ≤ stT287 267 := by
  have hc : ((-481171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294472321461/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-481171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c268 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-124999/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1961013/2500000) (δ := 14539/1000000000) (ψ := -744563/1000000) 287 256
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t268 : ((-4772689047/78125000000 : ℚ) : ℝ) ≤ stT287 268 := by
  have hc : ((-250023/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4772689047/78125000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-250023/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c269 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-477601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1034359/2000000) (δ := 14539/1000000000) (ψ := -744563/1000000) 287 256
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t269 : ((-291259554411/10000000000000 : ℚ) : ℝ) ≤ stT287 269 := by
  have hc : ((-477701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291259554411/10000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-477701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c270 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((537121/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3921/15625) (δ := 3591/250000000) (ψ := -744563/1000000) 287 256
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t270 : ((16341012009/500000000000 : ℚ) : ℝ) ≤ stT287 270 := by
  have hc : ((537021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16341012009/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((537021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c271 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((998363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71543/5000000) (δ := 14439/1000000000) (ψ := -744563/1000000) 287 256
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t271 : ((18950026529/312500000000 : ℚ) : ℝ) ≤ stT287 271 := by
  have hc : ((998263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18950026529/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((998263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c272 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((220397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1392891/5000000) (δ := 14439/1000000000) (ψ := -744563/1000000) 287 256
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t272 : ((133604979633/5000000000000 : ℚ) : ℝ) ≤ stT287 272 := by
  have hc : ((220347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133604979633/5000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((220347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c273 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-561933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677349/1250000) (δ := 14539/1000000000) (ψ := -744563/1000000) 287 256
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t273 : ((-85039527131/2500000000000 : ℚ) : ℝ) ≤ stT287 273 := by
  have hc : ((-562033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85039527131/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-562033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c274 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-199433/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533141/2000000) (δ := 1807/125000000) (ψ := -744563/1000000) 287 257
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t274 : ((-120494144719/2000000000000 : ℚ) : ℝ) ≤ stT287 274 := by
  have hc : ((-199453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120494144719/2000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-199453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c275 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-434941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1262981/2500000) (δ := 3589/250000000) (ψ := -744563/1000000) 287 257
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t275 : ((-262339728943/10000000000000 : ℚ) : ℝ) ≤ stT287 275 := by
  have hc : ((-435041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262339728943/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-435041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c276 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((557839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1223771/5000000) (δ := 14547/1000000000) (ψ := -744563/1000000) 287 257
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t276 : ((335719278531/10000000000000 : ℚ) : ℝ) ≤ stT287 276 := by
  have hc : ((557739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335719278531/10000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((557739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c277 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((998261/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1843/125000) (δ := 14447/1000000000) (ψ := -744563/1000000) 287 257
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t277 : ((599736053401/10000000000000 : ℚ) : ℝ) ≤ stT287 277 := by
  have hc : ((998161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((599736053401/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((998161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c278 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((229819/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2733023/10000000) (δ := 14447/1000000000) (ψ := -744563/1000000) 287 257
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t278 : ((1722578193/62500000000 : ℚ) : ℝ) ≤ stT287 278 := by
  have hc : ((229769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1722578193/62500000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((229769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c279 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-52517/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2654639/5000000) (δ := 1807/125000000) (ψ := -744563/1000000) 287 257
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t279 : ((-6289425399/200000000000 : ℚ) : ℝ) ≤ stT287 279 := by
  have hc : ((-52527/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6289425399/200000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-52527/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c280 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-24999/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3915771/5000000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 258
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t280 : ((-5976508569/100000000000 : ℚ) : ℝ) ≤ stT287 280 := by
  have hc : ((-50003/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5976508569/100000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-50003/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c281 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-512991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2636827/5000000) (δ := 7227/500000000) (ψ := -744563/1000000) 287 258
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t281 : ((-6121688721/200000000000 : ℚ) : ℝ) ≤ stT287 281 := by
  have hc : ((-513091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6121688721/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-513091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c282 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((231277/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2724807/10000000) (δ := 7227/500000000) (ψ := -744563/1000000) 287 258
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t282 : ((137693597457/5000000000000 : ℚ) : ℝ) ≤ stT287 282 := by
  have hc : ((231227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137693597457/5000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((231227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c283 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((997263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185001/10000000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 258
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t283 : ((296375789697/5000000000000 : ℚ) : ℝ) ≤ stT287 283 := by
  have hc : ((997163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296375789697/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((997163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c284 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((591109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2345909/10000000) (δ := 7227/500000000) (ψ := -744563/1000000) 287 258
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t284 : ((35069883051/1000000000000 : ℚ) : ℝ) ≤ stT287 284 := by
  have hc : ((591009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35069883051/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((591009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c285 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-183761/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4867849/10000000) (δ := 14549/1000000000) (ψ := -744563/1000000) 287 258
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t285 : ((-108880262039/5000000000000 : ℚ) : ℝ) ≤ stT287 285 := by
  have hc : ((-183811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108880262039/5000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-183811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c286 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-982159/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7381037/10000000) (δ := 7227/500000000) (ψ := -744563/1000000) 287 258
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t286 : ((-580822516067/10000000000000 : ℚ) : ℝ) ≤ stT287 286 := by
  have hc : ((-982259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580822516067/10000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-982259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c287 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-687637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1164513/2000000) (δ := 7271/500000000) (ψ := -744563/1000000) 287 259
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t287 : ((-202979385917/5000000000000 : ℚ) : ℝ) ≤ stT287 287 := by
  have hc : ((-687737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202979385917/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-687737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c288 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((59429/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -831739/2500000) (δ := 14361/1000000000) (ψ := -744563/1000000) 287 259
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t288 : ((1750205201/125000000000 : ℚ) : ℝ) ≤ stT287 288 := by
  have hc : ((14851/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1750205201/125000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((14851/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c289 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((944087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419979/5000000) (δ := 7271/500000000) (ψ := -744563/1000000) 287 259
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t289 : ((111057238589/2000000000000 : ℚ) : ℝ) ≤ stT287 289 := by
  have hc : ((943987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111057238589/2000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((943987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c290 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((792803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1638503/10000000) (δ := 14461/1000000000) (ψ := -744563/1000000) 287 259
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t290 : ((23274552783/500000000000 : ℚ) : ℝ) ≤ stT287 290 := by
  have hc : ((792703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23274552783/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((792703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c291 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-72481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4108353/10000000) (δ := 14361/1000000000) (ψ := -744563/1000000) 287 259
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t291 : ((-42547780591/10000000000000 : ℚ) : ℝ) ≤ stT287 291 := by
  have hc : ((-72581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42547780591/10000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-72581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c292 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-870947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410613/625000) (δ := 7271/500000000) (ψ := -744563/1000000) 287 259
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t292 : ((-254870965341/5000000000000 : ℚ) : ℝ) ≤ stT287 292 := by
  have hc : ((-871047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254870965341/5000000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-871047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c293 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-446343/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3342583/5000000) (δ := 2887/200000000) (ψ := -744563/1000000) 287 260
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t293 : ((-260785915351/5000000000000 : ℚ) : ℝ) ≤ stT287 293 := by
  have hc : ((-446393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-260785915351/5000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-446393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c294 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-7819/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060143/2500000) (δ := 2907/200000000) (ψ := -744563/1000000) 287 260
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t294 : ((-4563779703/625000000000 : ℚ) : ℝ) ≤ stT287 294 := by
  have hc : ((-31301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4563779703/625000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-31301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c295 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((750689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1804229/10000000) (δ := 2907/200000000) (ψ := -744563/1000000) 287 260
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t295 : ((218504714379/5000000000000 : ℚ) : ℝ) ≤ stT287 295 := by
  have hc : ((750589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218504714379/5000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((750589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c296 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((38761/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 623863/10000000) (δ := 2887/200000000) (ψ := -744563/1000000) 287 260
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t296 : ((11263520583/200000000000 : ℚ) : ℝ) ≤ stT287 296 := by
  have hc : ((38757/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11263520583/200000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((38757/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c297 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((345983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121751/400000) (δ := 2907/200000000) (ψ := -744563/1000000) 287 260
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t297 : ((100350688907/5000000000000 : ℚ) : ℝ) ≤ stT287 297 := by
  have hc : ((345883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100350688907/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((345883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c298 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-28701/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1363877/2500000) (δ := 2887/200000000) (ψ := -744563/1000000) 287 260
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t298 : ((-1662895521/50000000000 : ℚ) : ℝ) ≤ stT287 298 := by
  have hc : ((-14353/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1662895521/50000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-14353/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c299 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-499999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3924379/5000000) (δ := 579/40000000) (ψ := -744563/1000000) 287 261
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t299 : ((-57837167487/1000000000000 : ℚ) : ℝ) ≤ stT287 299 := by
  have hc : ((-500049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57837167487/1000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-500049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c300 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-57323/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2726549/5000000) (δ := 227/15625000) (ψ := -744563/1000000) 287 261
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t300 : ((-33101264883/1000000000000 : ℚ) : ℝ) ≤ stT287 300 := by
  have hc : ((-57333/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33101264883/1000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-57333/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c301 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((168927/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3065401/10000000) (δ := 23/1600000) (ψ := -744563/1000000) 287 261
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t301 : ((9733901403/500000000000 : ℚ) : ℝ) ≤ stT287 301 := by
  have hc : ((168877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9733901403/500000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((168877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c302 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((120329/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -685597/10000000) (δ := 23/1600000) (ψ := -744563/1000000) 287 261
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t302 : ((27693730071/500000000000 : ℚ) : ℝ) ≤ stT287 302 := by
  have hc : ((240633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27693730071/500000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((240633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c303 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((781003/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 843157/5000000) (δ := 227/15625000) (ψ := -744563/1000000) 287 261
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t303 : ((112154069763/2500000000000 : ℚ) : ℝ) ≤ stT287 303 := by
  have hc : ((780903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112154069763/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((780903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c304 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-24673/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 810081/2000000) (δ := 3607/250000000) (ψ := -744563/1000000) 287 261
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t304 : ((-708981471/250000000000 : ℚ) : ℝ) ≤ stT287 304 := by
  have hc : ((-24723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-708981471/250000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-24723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c305 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-837053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 256267/400000) (δ := 3607/250000000) (ψ := -744563/1000000) 287 261
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t305 : ((-479352970647/10000000000000 : ℚ) : ℝ) ≤ stT287 305 := by
  have hc : ((-837153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-479352970647/10000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-837153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c306 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-187141/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434539/625000) (δ := 363/25000000) (ψ := -744563/1000000) 287 262
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t306 : ((-53496415791/1000000000000 : ℚ) : ℝ) ≤ stT287 306 := by
  have hc : ((-187161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53496415791/1000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-187161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c307 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-10819/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1152927/2500000) (δ := 14383/1000000000) (ψ := -744563/1000000) 287 262
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t307 : ((-6177021613/400000000000 : ℚ) : ℝ) ≤ stT287 307 := by
  have hc : ((-10823/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6177021613/400000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-10823/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c308 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((9573/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139199/5000000) (δ := 14383/1000000000) (ψ := -744563/1000000) 287 262
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t308 : ((43630593843/1250000000000 : ℚ) : ℝ) ≤ stT287 308 := by
  have hc : ((153143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43630593843/1250000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((153143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c309 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((49991/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23689/5000000) (δ := 721/50000000) (ψ := -744563/1000000) 287 262
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t309 : ((177725223/3125000000 : ℚ) : ℝ) ≤ stT287 309 := by
  have hc : ((24993/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177725223/3125000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((24993/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c310 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((584731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2365621/10000000) (δ := 14483/1000000000) (ψ := -744563/1000000) 287 262
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t310 : ((332047607391/10000000000000 : ℚ) : ℝ) ≤ stT287 310 := by
  have hc : ((584631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332047607391/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((584631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c311 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-147661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4676473/10000000) (δ := 14383/1000000000) (ψ := -744563/1000000) 287 262
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t311 : ((-10469903391/625000000000 : ℚ) : ℝ) ≤ stT287 311 := by
  have hc : ((-147711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10469903391/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-147711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c312 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-234871/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6979791/10000000) (δ := 363/25000000) (ψ := -744563/1000000) 287 262
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t312 : ((-8311486659/156250000000 : ℚ) : ℝ) ≤ stT287 312 := by
  have hc : ((-14681/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8311486659/156250000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-14681/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c313 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-842589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1608043/2500000) (δ := 14413/1000000000) (ψ := -744563/1000000) 287 263
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t313 : ((-238158237113/5000000000000 : ℚ) : ℝ) ≤ stT287 313 := by
  have hc : ((-842689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238158237113/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-842689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c314 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-86491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414349/1000000) (δ := 1449/100000000) (ψ := -744563/1000000) 287 263
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t314 : ((-48866158803/10000000000000 : ℚ) : ℝ) ≤ stT287 314 := by
  have hc : ((-86591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48866158803/10000000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-86591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c315 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((91901/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232757/1250000) (δ := 14513/1000000000) (ψ := -744563/1000000) 287 263
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t315 : ((25886644443/625000000000 : ℚ) : ℝ) ≤ stT287 315 := by
  have hc : ((183777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25886644443/625000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((183777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c316 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((986443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103033/2500000) (δ := 14513/1000000000) (ψ := -744563/1000000) 287 263
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t316 : ((554860350249/10000000000000 : ℚ) : ℝ) ≤ stT287 316 := by
  have hc : ((986343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((554860350249/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((986343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c317 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((239347/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1339537/5000000) (δ := 1449/100000000) (ψ := -744563/1000000) 287 263
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t317 : ((26880471307/1000000000000 : ℚ) : ℝ) ≤ stT287 317 := by
  have hc : ((239297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26880471307/1000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((239297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c318 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-196903/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154341/312500) (δ := 1449/100000000) (ψ := -744563/1000000) 287 263
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t318 : ((-110445924669/5000000000000 : ℚ) : ℝ) ≤ stT287 318 := by
  have hc : ((-196953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110445924669/5000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-196953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c319 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-965117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3595859/5000000) (δ := 14413/1000000000) (ψ := -744563/1000000) 287 263
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t319 : ((-540418241781/10000000000000 : ℚ) : ℝ) ≤ stT287 319 := by
  have hc : ((-965217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-540418241781/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-965217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c320 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-806051/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3135307/5000000) (δ := 7253/500000000) (ψ := -744563/1000000) 287 264
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t320 : ((-450652113567/10000000000000 : ℚ) : ℝ) ≤ stT287 320 := by
  have hc : ((-806151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450652113567/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-806151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c321 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-41939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -403187/1000000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 264
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t321 : ((-11731949847/5000000000000 : ℚ) : ℝ) ≤ stT287 321 := by
  have hc : ((-42039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11731949847/5000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-42039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c322 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((187941/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900079/5000000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 264
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t322 : ((13090181581/312500000000 : ℚ) : ℝ) ≤ stT287 322 := by
  have hc : ((46979/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13090181581/312500000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((46979/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c323 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((985607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212333/5000000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 264
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t323 : ((274174945949/5000000000000 : ℚ) : ℝ) ≤ stT287 323 := by
  have hc : ((985507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274174945949/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((985507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c324 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((491451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1321301/5000000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 264
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t324 : ((54594500961/2000000000000 : ℚ) : ℝ) ≤ stT287 324 := by
  have hc : ((491351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54594500961/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((491351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c325 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-181117/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97073/200000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 264
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t325 : ((-100493516067/5000000000000 : ℚ) : ℝ) ≤ stT287 325 := by
  have hc : ((-181167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100493516067/5000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-181167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c326 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-474867/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7057953/10000000) (δ := 7253/500000000) (ψ := -744563/1000000) 287 264
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t326 : ((-263032305533/5000000000000 : ℚ) : ℝ) ≤ stT287 326 := by
  have hc : ((-474917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263032305533/5000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-474917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c327 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-84693/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6452451/10000000) (δ := 14399/1000000000) (ψ := -744563/1000000) 287 265
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t327 : ((-23420464203/500000000000 : ℚ) : ℝ) ≤ stT287 327 := by
  have hc : ((-84703/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23420464203/500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-84703/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c328 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-133431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -852313/2000000) (δ := 14499/1000000000) (ψ := -744563/1000000) 287 265
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t328 : ((-36865104949/5000000000000 : ℚ) : ℝ) ≤ stT287 328 := by
  have hc : ((-133531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36865104949/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-133531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c329 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((8427/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2077423/10000000) (δ := 14399/1000000000) (ψ := -744563/1000000) 287 265
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t329 : ((18581036851/500000000000 : ℚ) : ℝ) ≤ stT287 329 := by
  have hc : ((33703/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18581036851/500000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((33703/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c330 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((499599/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50059/5000000) (δ := 3601/250000000) (ψ := -744563/1000000) 287 265
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t330 : ((274992233069/5000000000000 : ℚ) : ℝ) ≤ stT287 330 := by
  have hc : ((499549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274992233069/5000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((499549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c331 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((61499/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1135529/5000000) (δ := 1813/125000000) (ψ := -744563/1000000) 287 265
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t331 : ((33797367361/1000000000000 : ℚ) : ℝ) ≤ stT287 331 := by
  have hc : ((61489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33797367361/1000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((61489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c332 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-201991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1108867/2500000) (δ := 14399/1000000000) (ψ := -744563/1000000) 287 265
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t332 : ((-55455993401/5000000000000 : ℚ) : ℝ) ≤ stT287 332 := by
  have hc : ((-202091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55455993401/5000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-202091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c333 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-54721/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6593349/10000000) (δ := 14499/1000000000) (ψ := -744563/1000000) 287 265
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t333 : ((-119961475273/2500000000000 : ℚ) : ℝ) ≤ stT287 333 := by
  have hc : ((-218909/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119961475273/2500000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-218909/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c334 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-234297/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -696319/1000000) (δ := 14411/1000000000) (ψ := -744563/1000000) 287 266
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t334 : ((-8013460917/156250000000 : ℚ) : ℝ) ≤ stT287 334 := by
  have hc : ((-117161/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8013460917/156250000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-117161/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c335 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-348963/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602269/1250000) (δ := 14411/1000000000) (ψ := -744563/1000000) 287 266
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t335 : ((-190713711617/10000000000000 : ℚ) : ℝ) ≤ stT287 335 := by
  have hc : ((-349063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190713711617/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-349063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c336 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((478519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669893/2500000) (δ := 3623/250000000) (ψ := -744563/1000000) 287 266
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t336 : ((32624826867/1250000000000 : ℚ) : ℝ) ≤ stT287 336 := by
  have hc : ((478419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32624826867/1250000000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((478419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c337 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((244033/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -109461/2000000) (δ := 14411/1000000000) (ψ := -744563/1000000) 287 266
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t337 : ((8307465867/156250000000 : ℚ) : ℝ) ≤ stT287 337 := by
  have hc : ((30501/31250 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8307465867/156250000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((30501/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c338 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((50449/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98661/625000) (δ := 14511/1000000000) (ψ := -744563/1000000) 287 266
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t338 : ((13718612061/312500000000 : ℚ) : ℝ) ≤ stT287 338 := by
  have hc : ((201771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13718612061/312500000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((201771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c339 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((45677/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1849143/5000000) (δ := 14411/1000000000) (ψ := -744563/1000000) 287 266
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t339 : ((39649863/8000000000 : ℚ) : ℝ) ≤ stT287 339 := by
  have hc : ((45627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39649863/8000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((45627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c340 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-68447/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2905841/5000000) (δ := 1799/125000000) (ψ := -744563/1000000) 287 266
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t340 : ((-37126079439/1000000000000 : ℚ) : ℝ) ≤ stT287 340 := by
  have hc : ((-68457/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37126079439/1000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-68457/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c341 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-62479/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7789127/10000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 267
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t341 : ((-135350799671/2500000000000 : ℚ) : ℝ) ≤ stT287 341 := by
  have hc : ((-249941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135350799671/2500000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-249941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c342 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-647601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711009/1250000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 267
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t342 : ((-350237191039/10000000000000 : ℚ) : ℝ) ≤ stT287 342 := by
  have hc : ((-647701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350237191039/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-647701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c343 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((213/1600 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3593187/10000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 267
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t343 : ((2873068629/400000000000 : ℚ) : ℝ) ≤ stT287 343 := by
  have hc : ((5321/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2873068629/400000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((5321/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c344 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((41217/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1504401/10000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 267
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t344 : ((5554996389/125000000000 : ℚ) : ℝ) ≤ stT287 344 := by
  have hc : ((10303/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5554996389/125000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((10303/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c345 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((973359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289179/5000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 267
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t345 : ((523984153679/10000000000000 : ℚ) : ℝ) ≤ stT287 345 := by
  have hc : ((973259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523984153679/10000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((973259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c346 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((6089/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1327509/5000000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 267
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t346 : ((13091170653/500000000000 : ℚ) : ℝ) ≤ stT287 346 := by
  have hc : ((24351/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13091170653/500000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((24351/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c347 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-62817/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4725723/10000000) (δ := 2877/200000000) (ψ := -744563/1000000) 287 267
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t347 : ((-33732723873/2000000000000 : ℚ) : ℝ) ≤ stT287 347 := by
  have hc : ((-62837/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33732723873/2000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-62837/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c348 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-113859/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6790473/10000000) (δ := 7209/500000000) (ψ := -744563/1000000) 287 267
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t348 : ((-122083229351/2500000000000 : ℚ) : ℝ) ≤ stT287 348 := by
  have hc : ((-227743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122083229351/2500000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-227743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c349 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-921783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53583/78125) (δ := 7213/500000000) (ψ := -744563/1000000) 287 268
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t349 : ((-61684113413/1250000000000 : ℚ) : ℝ) ≤ stT287 349 := by
  have hc : ((-921883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61684113413/1250000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-921883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c350 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-43037/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4805713/10000000) (δ := 7213/500000000) (ψ := -744563/1000000) 287 268
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t350 : ((-46021895777/2500000000000 : ℚ) : ℝ) ≤ stT287 350 := by
  have hc : ((-86099/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46021895777/2500000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-86099/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c351 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((450523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1379307/5000000) (δ := 14377/1000000000) (ψ := -744563/1000000) 287 268
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t351 : ((187826391/7812500000 : ℚ) : ℝ) ≤ stT287 351 := by
  have hc : ((450423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187826391/7812500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((450423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c352 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((959109/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -358699/5000000) (δ := 7213/500000000) (ψ := -744563/1000000) 287 268
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t352 : ((511152756009/10000000000000 : ℚ) : ℝ) ≤ stT287 352 := by
  have hc : ((959009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511152756009/10000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((959009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c353 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((864203/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 659039/5000000) (δ := 7263/500000000) (ψ := -744563/1000000) 287 268
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t353 : ((229957682669/5000000000000 : ℚ) : ℝ) ≤ stT287 353 := by
  have hc : ((864103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229957682669/5000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((864103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c354 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((57401/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3347813/10000000) (δ := 14477/1000000000) (ψ := -744563/1000000) 287 268
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t354 : ((476484371/39062500000 : ℚ) : ℝ) ≤ stT287 354 := by
  have hc : ((3586/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476484371/39062500000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((3586/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c355 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-109253/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5371737/10000000) (δ := 14477/1000000000) (ψ := -744563/1000000) 287 268
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t355 : ((-11599219677/400000000000 : ℚ) : ℝ) ≤ stT287 355 := by
  have hc : ((-109273/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11599219677/400000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-109273/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c356 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-61427/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1478013/2000000) (δ := 7213/500000000) (ψ := -744563/1000000) 287 268
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t356 : ((-130238244267/2500000000000 : ℚ) : ℝ) ≤ stT287 356 := by
  have hc : ((-245733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130238244267/2500000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-245733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c357 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-814187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6305311/10000000) (δ := 1437/100000000) (ψ := -744563/1000000) 287 269
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t357 : ((-430967094759/10000000000000 : ℚ) : ℝ) ≤ stT287 357 := by
  have hc : ((-814287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-430967094759/10000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-814287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c358 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-73993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53729/125000) (δ := 1437/100000000) (ψ := -744563/1000000) 287 269
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t358 : ((-39132984231/5000000000000 : ℚ) : ℝ) ≤ stT287 358 := by
  have hc : ((-74043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39132984231/5000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-74043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c359 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((303399/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91877/400000) (δ := 14533/1000000000) (ψ := -744563/1000000) 287 269
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t359 : ((160101231871/5000000000000 : ℚ) : ℝ) ≤ stT287 359 := by
  have hc : ((303349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160101231871/5000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((303349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c360 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((496379/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2352/78125) (δ := 1447/100000000) (ψ := -744563/1000000) 287 269
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t360 : ((130794107067/2500000000000 : ℚ) : ℝ) ≤ stT287 360 := by
  have hc : ((496329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130794107067/2500000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((496329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c361 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((780277/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844609/5000000) (δ := 14533/1000000000) (ψ := -744563/1000000) 287 269
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t361 : ((82123771551/2000000000000 : ℚ) : ℝ) ≤ stT287 361 := by
  have hc : ((780177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82123771551/2000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((780177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c362 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((101009/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1837019/5000000) (δ := 14433/1000000000) (ψ := -744563/1000000) 287 269
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t362 : ((13259139873/2500000000000 : ℚ) : ℝ) ≤ stT287 362 := by
  have hc : ((100909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13259139873/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((100909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c363 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-636951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5653333/10000000) (δ := 1447/100000000) (ψ := -744563/1000000) 287 269
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t363 : ((-5224455251/156250000000 : ℚ) : ℝ) ≤ stT287 363 := by
  have hc : ((-637051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5224455251/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-637051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c364 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-62243/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953397/1250000) (δ := 14433/1000000000) (ψ := -744563/1000000) 287 269
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t364 : ((-130510034571/2500000000000 : ℚ) : ℝ) ≤ stT287 364 := by
  have hc : ((-248997/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130510034571/2500000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-248997/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c365 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-191747/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3056163/5000000) (δ := 361/25000000) (ψ := -744563/1000000) 287 270
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t365 : ((-784203651/19531250000 : ℚ) : ℝ) ≤ stT287 365 := by
  have hc : ((-47943/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-784203651/19531250000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-47943/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c366 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-17757/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2074623/5000000) (δ := 361/25000000) (ψ := -744563/1000000) 287 270
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t366 : ((-9292197893/2000000000000 : ℚ) : ℝ) ≤ stT287 366 := by
  have hc : ((-17777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9292197893/2000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-17777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c367 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((319877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2191547/10000000) (δ := 727/50000000) (ψ := -744563/1000000) 287 270
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t367 : ((33389618973/1000000000000 : ℚ) : ℝ) ≤ stT287 367 := by
  have hc : ((319827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33389618973/1000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((319827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c368 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((248857/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119579/5000000) (δ := 361/25000000) (ψ := -744563/1000000) 287 270
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t368 : ((63336249/1220703125 : ℚ) : ℝ) ≤ stT287 368 := by
  have hc : ((15552/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63336249/1220703125 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((15552/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c369 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((96947/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 853961/5000000) (δ := 727/50000000) (ψ := -744563/1000000) 287 270
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t369 : ((100924130151/2500000000000 : ℚ) : ℝ) ≤ stT287 369 := by
  have hc : ((193869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100924130151/2500000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((193869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c370 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((13833/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912441/2500000) (δ := 727/50000000) (ψ := -744563/1000000) 287 270
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t370 : ((114958919/20000000000 : ℚ) : ℝ) ≤ stT287 370 := by
  have hc : ((27641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114958919/20000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((27641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c371 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-616053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 698287/1250000) (δ := 14363/1000000000) (ψ := -744563/1000000) 287 270
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t371 : ((-12795649351/400000000000 : ℚ) : ℝ) ≤ stT287 371 := by
  have hc : ((-616153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12795649351/400000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-616153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c372 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-198193/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7517663/10000000) (δ := 727/50000000) (ψ := -744563/1000000) 287 270
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t372 : ((-25692170847/500000000000 : ℚ) : ℝ) ≤ stT287 372 := by
  have hc : ((-198213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25692170847/500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-198213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c373 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-402253/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62641/100000) (δ := 14447/1000000000) (ψ := -744563/1000000) 287 271
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t373 : ((-208304849643/5000000000000 : ℚ) : ℝ) ≤ stT287 373 := by
  have hc : ((-402303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208304849643/5000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-402303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c374 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-165691/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4343137/10000000) (δ := 14547/1000000000) (ψ := -744563/1000000) 287 271
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t374 : ((-2679016769/312500000000 : ℚ) : ℝ) ≤ stT287 374 := by
  have hc : ((-165791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2679016769/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-165791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c375 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((282287/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2427197/10000000) (δ := 14447/1000000000) (ψ := -744563/1000000) 287 271
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t375 : ((145746340089/5000000000000 : ℚ) : ℝ) ≤ stT287 375 := by
  have hc : ((282237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145746340089/5000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((282237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c376 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((48937/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -516423/10000000) (δ := 3589/250000000) (ψ := -744563/1000000) 287 271
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t376 : ((630868043/12500000000 : ℚ) : ℝ) ≤ stT287 376 := by
  have hc : ((12233/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630868043/12500000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((12233/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c377 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((84953/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389257/10000000) (δ := 3589/250000000) (ψ := -744563/1000000) 287 271
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t377 : ((21873926759/500000000000 : ℚ) : ℝ) ≤ stT287 377 := by
  have hc : ((84943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21873926759/500000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((84943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c378 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((252081/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 657983/2000000) (δ := 14547/1000000000) (ψ := -744563/1000000) 287 271
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t378 : ((16200614433/1250000000000 : ℚ) : ℝ) ≤ stT287 378 := by
  have hc : ((251981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16200614433/1250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((251981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c379 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-120613/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5185621/10000000) (δ := 1807/125000000) (ψ := -744563/1000000) 287 271
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t379 : ((-15491909727/625000000000 : ℚ) : ℝ) ≤ stT287 379 := by
  have hc : ((-60319/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15491909727/625000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-60319/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c380 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-475999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3538117/5000000) (δ := 14447/1000000000) (ψ := -744563/1000000) 287 271
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t380 : ((-24420837651/500000000000 : ℚ) : ℝ) ≤ stT287 380 := by
  have hc : ((-476049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24420837651/500000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-476049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c381 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-903399/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1686517/2500000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 272
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t381 : ((-115719248421/2500000000000 : ℚ) : ℝ) ≤ stT287 381 := by
  have hc : ((-903499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115719248421/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-903499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c382 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-45821/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973057/2000000) (δ := 7177/500000000) (ψ := -744563/1000000) 287 272
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t382 : ((-9380192443/500000000000 : ℚ) : ℝ) ≤ stT287 382 := by
  have hc : ((-91667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9380192443/500000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-91667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c383 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((18313/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119581/400000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 272
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t383 : ((4567846/244140625 : ℚ) : ℝ) ≤ stT287 383 := by
  have hc : ((4577/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4567846/244140625 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((4577/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c384 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((901563/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279643/2500000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 272
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t384 : ((46002558353/1000000000000 : ℚ) : ℝ) ≤ stT287 384 := by
  have hc : ((901463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46002558353/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((901463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c385 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((955631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373751/5000000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 272
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t385 : ((486983507557/10000000000000 : ℚ) : ℝ) ≤ stT287 385 := by
  have hc : ((955531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486983507557/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((955531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c386 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((503217/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2608697/10000000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 272
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t386 : ((128039754681/5000000000000 : ℚ) : ℝ) ≤ stT287 386 := by
  have hc : ((503117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128039754681/5000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((503117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c387 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-10679/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 893017/2000000) (δ := 7177/500000000) (ψ := -744563/1000000) 287 272
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t387 : ((-1357746759/125000000000 : ℚ) : ℝ) ≤ stT287 387 := by
  have hc : ((-2671/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1357746759/125000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-2671/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c388 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-12763/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6316737/10000000) (δ := 14449/1000000000) (ψ := -744563/1000000) 287 272
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t388 : ((-51841892021/1250000000000 : ℚ) : ℝ) ≤ stT287 388 := by
  have hc : ((-204233/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51841892021/1250000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-204233/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c389 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-496171/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7544381/10000000) (δ := 7181/500000000) (ψ := -744563/1000000) 287 273
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t389 : ((-251594467641/5000000000000 : ℚ) : ℝ) ≤ stT287 389 := by
  have hc : ((-496221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251594467641/5000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-496221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c390 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-651919/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44549/78125) (δ := 14541/1000000000) (ψ := -744563/1000000) 287 273
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t390 : ((-33016286103/1000000000000 : ℚ) : ℝ) ≤ stT287 390 := by
  have hc : ((-652019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33016286103/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-652019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c391 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((4967/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1932449/5000000) (δ := 14541/1000000000) (ψ := -744563/1000000) 287 273
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t391 : ((2501801787/2000000000000 : ℚ) : ℝ) ≤ stT287 391 := by
  have hc : ((4947/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2501801787/2000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((4947/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c392 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((687413/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2032187/10000000) (δ := 7231/500000000) (ψ := -744563/1000000) 287 273
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t392 : ((86786325197/2500000000000 : ℚ) : ℝ) ≤ stT287 392 := by
  have hc : ((687313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86786325197/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((687313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c393 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((249167/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204141/10000000) (δ := 14441/1000000000) (ψ := -744563/1000000) 287 273
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t393 : ((62837723243/1250000000000 : ℚ) : ℝ) ≤ stT287 393 := by
  have hc : ((124571/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62837723243/1250000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((124571/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c394 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((199369/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 809621/5000000) (δ := 7181/500000000) (ψ := -744563/1000000) 287 273
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t394 : ((392296533/9765625000 : ℚ) : ℝ) ≤ stT287 394 := by
  have hc : ((12459/15625 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392296533/9765625000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((12459/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c395 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((194367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3437961/10000000) (δ := 7181/500000000) (ψ := -744563/1000000) 287 273
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t395 : ((48873109059/5000000000000 : ℚ) : ℝ) ≤ stT287 395 := by
  have hc : ((194267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48873109059/5000000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((194267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c396 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-63199/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16413/31250) (δ := 7231/500000000) (ψ := -744563/1000000) 287 273
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t396 : ((-63529959537/2500000000000 : ℚ) : ℝ) ≤ stT287 396 := by
  have hc : ((-126423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63529959537/2500000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-126423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c397 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-950201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1412339/2000000) (δ := 7231/500000000) (ψ := -744563/1000000) 287 273
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t397 : ((-238471383843/5000000000000 : ℚ) : ℝ) ≤ stT287 397 := by
  have hc : ((-950301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238471383843/5000000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-950301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c398 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-183811/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3420591/5000000) (δ := 14369/1000000000) (ψ := -744563/1000000) 287 274
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t398 : ((-18429241581/400000000000 : ℚ) : ℝ) ≤ stT287 398 := by
  have hc : ((-183831/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18429241581/400000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-183831/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c399 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-43089/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -315043/625000) (δ := 7267/500000000) (ψ := -744563/1000000) 287 274
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t399 : ((-21576523073/1000000000000 : ℚ) : ℝ) ≤ stT287 399 := by
  have hc : ((-43099/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21576523073/1000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-43099/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c400 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((8423/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3244713/10000000) (δ := 14469/1000000000) (ψ := -744563/1000000) 287 274
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t400 : ((67359/5000000 : ℚ) : ℝ) ≤ stT287 400 := by
  have hc : ((67359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67359/5000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((67359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c401 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((835763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -363297/2500000) (δ := 7267/500000000) (ψ := -744563/1000000) 287 274
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t401 : ((26081877893/625000000000 : ℚ) : ℝ) ≤ stT287 401 := by
  have hc : ((835663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26081877893/625000000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((835663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c402 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((495549/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166909/5000000) (δ := 14369/1000000000) (ψ := -744563/1000000) 287 274
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t402 : ((123566054123/2500000000000 : ℚ) : ℝ) ≤ stT287 402 := by
  have hc : ((495499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123566054123/2500000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((495499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c403 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((13251/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2116447/10000000) (δ := 14469/1000000000) (ψ := -744563/1000000) 287 274
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t403 : ((1319958123/40000000000 : ℚ) : ℝ) ≤ stT287 403 := by
  have hc : ((13249/20000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1319958123/40000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((13249/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c404 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((2589/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3894627/10000000) (δ := 14369/1000000000) (ψ := -744563/1000000) 287 274
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t404 : ((639061871/1000000000000 : ℚ) : ℝ) ≤ stT287 404 := by
  have hc : ((2569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639061871/1000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((2569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c405 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-128319/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 566843/1000000) (δ := 7267/500000000) (ψ := -744563/1000000) 287 274
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t405 : ((-7971520307/250000000000 : ℚ) : ℝ) ≤ stT287 405 := by
  have hc : ((-128339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7971520307/250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-128339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c406 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-986179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7437857/10000000) (δ := 7217/500000000) (ψ := -744563/1000000) 287 274
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t406 : ((-122370594367/2500000000000 : ℚ) : ℝ) ≤ stT287 406 := by
  have hc : ((-986279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122370594367/2500000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-986279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c407 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-85793/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203283/312500) (δ := 1797/125000000) (ψ := -744563/1000000) 287 275
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t407 : ((-21265501323/500000000000 : ℚ) : ℝ) ≤ stT287 407 := by
  have hc : ((-85803/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21265501323/500000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-85803/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c408 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-64227/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4744311/10000000) (δ := 1797/125000000) (ψ := -744563/1000000) 287 275
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t408 : ((-15903509639/1000000000000 : ℚ) : ℝ) ≤ stT287 408 := by
  have hc : ((-64247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15903509639/1000000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-64247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c409 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((587/1600 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2987871/10000000) (δ := 1797/125000000) (ψ := -744563/1000000) 287 275
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t409 : ((1813585007/100000000000 : ℚ) : ℝ) ≤ stT287 409 := by
  have hc : ((14671/40000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1813585007/100000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((14671/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c410 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((55019/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154467/1250000) (δ := 1797/125000000) (ψ := -744563/1000000) 287 275
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t410 : ((13584408383/312500000000 : ℚ) : ℝ) ≤ stT287 410 := by
  have hc : ((220051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13584408383/312500000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((220051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c411 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((61193/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 256083/5000000) (δ := 3619/250000000) (ψ := -744563/1000000) 287 275
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t411 : ((120724639461/2500000000000 : ℚ) : ℝ) ≤ stT287 411 := by
  have hc : ((244747/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120724639461/2500000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((244747/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c412 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((619803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1127881/5000000) (δ := 14527/1000000000) (ψ := -744563/1000000) 287 275
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t412 : ((38163169849/1250000000000 : ℚ) : ℝ) ≤ stT287 412 := by
  have hc : ((619703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38163169849/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((619703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c413 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-27251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1997563/5000000) (δ := 1797/125000000) (ψ := -744563/1000000) 287 275
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t413 : ((-3364637967/2500000000000 : ℚ) : ℝ) ≤ stT287 413 := by
  have hc : ((-27351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3364637967/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-27351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c414 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-165097/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 716291/1250000) (δ := 1797/125000000) (ψ := -744563/1000000) 287 275
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t414 : ((-20288292457/625000000000 : ℚ) : ℝ) ≤ stT287 414 := by
  have hc : ((-82561/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20288292457/625000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-82561/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c415 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-493847/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 932671/1250000) (δ := 14527/1000000000) (ψ := -744563/1000000) 287 275
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t415 : ((-242444653257/5000000000000 : ℚ) : ℝ) ≤ stT287 415 := by
  have hc : ((-493897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242444653257/5000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-493897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c416 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-430471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1629947/2500000) (δ := 363/25000000) (ψ := -744563/1000000) 287 276
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t416 : ((-211080571611/5000000000000 : ℚ) : ℝ) ≤ stT287 416 := by
  have hc : ((-430521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211080571611/5000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-430521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c417 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-42631/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479707/1000000) (δ := 14383/1000000000) (ψ := -744563/1000000) 287 276
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t417 : ((-41765299761/2500000000000 : ℚ) : ℝ) ≤ stT287 417 := by
  have hc : ((-85287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41765299761/2500000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-85287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c418 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((332913/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1539257/5000000) (δ := 14383/1000000000) (ψ := -744563/1000000) 287 276
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t418 : ((32556766099/2000000000000 : ℚ) : ℝ) ≤ stT287 418 := by
  have hc : ((332813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32556766099/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((332813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c419 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((427403/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85253/625000) (δ := 721/50000000) (ψ := -744563/1000000) 287 276
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t419 : ((208775188443/5000000000000 : ℚ) : ℝ) ≤ stT287 419 := by
  have hc : ((427353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208775188443/5000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((427353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c420 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((49521/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346329/10000000) (δ := 14483/1000000000) (ψ := -744563/1000000) 287 276
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t420 : ((120806661/2500000000 : ℚ) : ℝ) ≤ stT287 420 := by
  have hc : ((12379/12500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120806661/2500000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((12379/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c421 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((42591/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410523/2000000) (δ := 363/25000000) (ψ := -744563/1000000) 287 276
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t421 : ((8301811843/250000000000 : ℚ) : ℝ) ≤ stT287 421 := by
  have hc : ((170339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8301811843/250000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((170339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c422 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((17197/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 938721/2500000) (δ := 721/50000000) (ψ := -744563/1000000) 287 276
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t422 : ((261224757/78125000000 : ℚ) : ℝ) ≤ stT287 422 := by
  have hc : ((4293/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261224757/78125000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((4293/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c423 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-573219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5453063/10000000) (δ := 721/50000000) (ψ := -744563/1000000) 287 276
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t423 : ((-278757444223/10000000000000 : ℚ) : ℝ) ≤ stT287 423 := by
  have hc : ((-573319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278757444223/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-573319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c424 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-960313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223353/312500) (δ := 14383/1000000000) (ψ := -744563/1000000) 287 276
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t424 : ((-466417850559/10000000000000 : ℚ) : ℝ) ≤ stT287 424 := by
  have hc : ((-960413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-466417850559/10000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-960413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c425 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-923607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6870453/10000000) (δ := 14513/1000000000) (ψ := -744563/1000000) 287 277
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t425 : ((-28004025119/625000000000 : ℚ) : ℝ) ≤ stT287 425 := by
  have hc : ((-923707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28004025119/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-923707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c426 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-481949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -648023/1250000) (δ := 1439/100000000) (ψ := -744563/1000000) 287 277
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t426 : ((-116776852299/5000000000000 : ℚ) : ℝ) ≤ stT287 426 := by
  have hc : ((-482049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116776852299/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-482049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c427 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((169233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1750931/5000000) (δ := 14413/1000000000) (ψ := -744563/1000000) 287 277
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t427 : ((81849040089/10000000000000 : ℚ) : ℝ) ≤ stT287 427 := by
  have hc : ((169133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81849040089/10000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((169133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c428 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((745559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -911779/5000000) (δ := 14513/1000000000) (ψ := -744563/1000000) 287 277
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t428 : ((45041378239/1250000000000 : ℚ) : ℝ) ≤ stT287 428 := by
  have hc : ((745459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45041378239/1250000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((745459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c429 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((998223/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2329/156250) (δ := 1439/100000000) (ψ := -744563/1000000) 287 277
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t429 : ((120474444223/2500000000000 : ℚ) : ℝ) ≤ stT287 429 := by
  have hc : ((998123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120474444223/2500000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((998123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c430 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((820449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1521499/10000000) (δ := 14413/1000000000) (ψ := -744563/1000000) 287 277
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t430 : ((197803371229/5000000000000 : ℚ) : ℝ) ≤ stT287 430 := by
  have hc : ((820349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197803371229/5000000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((820349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c431 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((291269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 797027/2500000) (δ := 14413/1000000000) (ψ := -744563/1000000) 287 277
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t431 : ((140251157427/10000000000000 : ℚ) : ℝ) ≤ stT287 431 := by
  have hc : ((291169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140251157427/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((291169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c432 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-180607/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2425457/5000000) (δ := 14513/1000000000) (ψ := -744563/1000000) 287 277
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t432 : ((-43459389891/2500000000000 : ℚ) : ℝ) ≤ stT287 432 := by
  have hc : ((-180657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43459389891/2500000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-180657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c433 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-858927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3254959/5000000) (δ := 1439/100000000) (ψ := -744563/1000000) 287 277
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t433 : ((-41282260539/1000000000000 : ℚ) : ℝ) ≤ stT287 433 := by
  have hc : ((-859027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41282260539/1000000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-859027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c434 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-992269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1885729/2500000) (δ := 14497/1000000000) (ψ := -744563/1000000) 287 278
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t434 : ((-29772062369/625000000000 : ℚ) : ℝ) ≤ stT287 434 := by
  have hc : ((-992369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29772062369/625000000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-992369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c435 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-707419/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589159/1000000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 278
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t435 : ((-42403736227/1250000000000 : ℚ) : ℝ) ≤ stT287 435 := by
  have hc : ((-707519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42403736227/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-707519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c436 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-126491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4244067/10000000) (δ := 7253/500000000) (ψ := -744563/1000000) 287 278
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t436 : ((-30313101087/5000000000000 : ℚ) : ℝ) ≤ stT287 436 := by
  have hc : ((-126591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30313101087/5000000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-126591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c437 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((506101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1300173/5000000) (δ := 7203/500000000) (ψ := -744563/1000000) 287 278
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t437 : ((60513165591/2500000000000 : ℚ) : ℝ) ≤ stT287 437 := by
  have hc : ((506001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60513165591/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((506001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c438 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((927131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -240071/2500000) (δ := 14497/1000000000) (ψ := -744563/1000000) 287 278
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t438 : ((221476049179/5000000000000 : ℚ) : ℝ) ≤ stT287 438 := by
  have hc : ((927031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221476049179/5000000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((927031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c439 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((963667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 337987/5000000) (δ := 7253/500000000) (ψ := -744563/1000000) 287 278
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t439 : ((459884512791/10000000000000 : ℚ) : ℝ) ≤ stT287 439 := by
  have hc : ((963567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459884512791/10000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((963567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c440 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((603111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154251/5000000) (δ := 7203/500000000) (ψ := -744563/1000000) 287 278
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t440 : ((287474037041/10000000000000 : ℚ) : ℝ) ≤ stT287 440 := by
  have hc : ((603011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((287474037041/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((603011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c441 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-4123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3937299/10000000) (δ := 14397/1000000000) (ψ := -744563/1000000) 287 278
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t441 : ((-2010954593/10000000000000 : ℚ) : ℝ) ≤ stT287 441 := by
  have hc : ((-4223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2010954593/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-4223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c442 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-608507/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1390609/2500000) (δ := 7253/500000000) (ψ := -744563/1000000) 287 278
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t442 : ((-72371284191/2500000000000 : ℚ) : ℝ) ≤ stT287 442 := by
  have hc : ((-608607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72371284191/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-608607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c443 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-192859/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1436783/2000000) (δ := 14497/1000000000) (ψ := -744563/1000000) 287 278
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t443 : ((-18327941217/400000000000 : ℚ) : ℝ) ≤ stT287 443 := by
  have hc : ((-192879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18327941217/400000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-192879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c444 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-464499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690623/1000000) (δ := 7249/500000000) (ψ := -744563/1000000) 287 279
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t444 : ((-220465199871/5000000000000 : ℚ) : ℝ) ≤ stT287 444 := by
  have hc : ((-464549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220465199871/5000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-464549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c445 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-5193/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529207/1000000) (δ := 7199/500000000) (ψ := -744563/1000000) 287 279
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t445 : ((-615548731/25000000000 : ℚ) : ℝ) ≤ stT287 445 := by
  have hc : ((-2597/5000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615548731/25000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-2597/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c446 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((98039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1840749/5000000) (δ := 7249/500000000) (ψ := -744563/1000000) 287 279
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t446 : ((46375389707/10000000000000 : ℚ) : ℝ) ≤ stT287 446 := by
  have hc : ((97939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46375389707/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((97939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c447 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((337499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414917/2000000) (δ := 7249/500000000) (ψ := -744563/1000000) 287 279
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t447 : ((159607640367/5000000000000 : ℚ) : ℝ) ≤ stT287 447 := by
  have hc : ((337449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159607640367/5000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((337449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c448 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((982291/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471187/10000000) (δ := 2901/200000000) (ψ := -744563/1000000) 287 279
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t448 : ((92808209781/2000000000000 : ℚ) : ℝ) ≤ stT287 448 := by
  have hc : ((982191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92808209781/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((982191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c449 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((224957/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1128551/10000000) (δ := 2901/200000000) (ψ := -744563/1000000) 287 279
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t449 : ((26537983457/625000000000 : ℚ) : ℝ) ≤ stT287 449 := by
  have hc : ((56233/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26537983457/625000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((56233/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c450 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((231283/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2724773/10000000) (δ := 2881/200000000) (ψ := -744563/1000000) 287 279
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t450 : ((27251040283/1250000000000 : ℚ) : ℝ) ≤ stT287 450 := by
  have hc : ((231233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27251040283/1250000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((231233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c451 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-155561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4317479/10000000) (δ := 7249/500000000) (ψ := -744563/1000000) 287 279
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t451 : ((-36648981501/5000000000000 : ℚ) : ℝ) ≤ stT287 451 := by
  have hc : ((-155661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36648981501/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-155661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c452 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-711649/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2953299/5000000) (δ := 7249/500000000) (ψ := -744563/1000000) 287 279
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t452 : ((-334778971389/10000000000000 : ℚ) : ℝ) ≤ stT287 452 := by
  have hc : ((-711749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334778971389/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-711749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c453 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-61847/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7492273/10000000) (δ := 7249/500000000) (ψ := -744563/1000000) 287 279
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t453 : ((-116244771333/2500000000000 : ℚ) : ℝ) ≤ stT287 453 := by
  have hc : ((-247413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116244771333/2500000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-247413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c454 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-883201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3316801/5000000) (δ := 907/62500000) (ψ := -744563/1000000) 287 280
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t454 : ((-103638589631/2500000000000 : ℚ) : ℝ) ≤ stT287 454 := by
  have hc : ((-883301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103638589631/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-883301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c455 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-54501/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5054887/10000000) (δ := 3603/250000000) (ψ := -744563/1000000) 287 280
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t455 : ((-6389091227/312500000000 : ℚ) : ℝ) ≤ stT287 455 := by
  have hc : ((-109027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6389091227/312500000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-109027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c456 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((11123/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434961/1250000) (δ := 14491/1000000000) (ψ := -744563/1000000) 287 280
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t456 : ((5205885091/625000000000 : ℚ) : ℝ) ≤ stT287 456 := by
  have hc : ((44467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5205885091/625000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((44467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c457 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((722627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -477001/2500000) (δ := 14391/1000000000) (ψ := -744563/1000000) 287 280
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t457 : ((16899184003/500000000000 : ℚ) : ℝ) ≤ stT287 457 := by
  have hc : ((722527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16899184003/500000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((722527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c458 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((990783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84923/2500000) (δ := 907/62500000) (ψ := -744563/1000000) 287 280
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t458 : ((462915454727/10000000000000 : ℚ) : ℝ) ≤ stT287 458 := by
  have hc : ((990683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462915454727/10000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((990683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c459 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((441143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1225247/10000000) (δ := 3603/250000000) (ψ := -744563/1000000) 287 280
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t459 : ((5147114217/125000000000 : ℚ) : ℝ) ≤ stT287 459 := by
  have hc : ((441093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5147114217/125000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((441093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c460 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((110119/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278667/1000000) (δ := 14491/1000000000) (ψ := -744563/1000000) 287 280
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t460 : ((6416443461/312500000000 : ℚ) : ℝ) ≤ stT287 460 := by
  have hc : ((55047/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6416443461/312500000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((55047/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c461 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-20793/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4344793/10000000) (δ := 14491/1000000000) (ψ := -744563/1000000) 287 280
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t461 : ((-19380198417/2500000000000 : ℚ) : ℝ) ≤ stT287 461 := by
  have hc : ((-41611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19380198417/2500000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-41611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c462 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-177411/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 368717/625000) (δ := 14491/1000000000) (ψ := -744563/1000000) 287 280
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t462 : ((-20637714237/625000000000 : ℚ) : ℝ) ≤ stT287 462 := by
  have hc : ((-44359/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20637714237/625000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-44359/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c463 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-987027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7450851/10000000) (δ := 3603/250000000) (ψ := -744563/1000000) 287 280
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t463 : ((-22937870099/500000000000 : ℚ) : ℝ) ≤ stT287 463 := by
  have hc : ((-987127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22937870099/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-987127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c464 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-896961/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3354553/5000000) (δ := 14419/1000000000) (ψ := -744563/1000000) 287 281
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t464 : ((-416450701579/10000000000000 : ℚ) : ℝ) ≤ stT287 464 := by
  have hc : ((-897061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416450701579/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-897061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c465 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-19/40 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12911/25000) (δ := 14519/1000000000) (ψ := -744563/1000000) 287 281
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t465 : ((-2203223989/100000000000 : ℚ) : ℝ) ≤ stT287 465 := by
  have hc : ((-4751/10000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2203223989/100000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-4751/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c466 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((12127/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3623067/10000000) (δ := 899/62500000) (ψ := -744563/1000000) 287 281
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t466 : ((5613091197/1000000000000 : ℚ) : ℝ) ≤ stT287 466 := by
  have hc : ((12117/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5613091197/1000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((12117/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c467 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((671909/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1042517/5000000) (δ := 899/62500000) (ψ := -744563/1000000) 287 281
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t467 : ((38859447987/1250000000000 : ℚ) : ℝ) ≤ stT287 467 := by
  have hc : ((671809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38859447987/1250000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((671809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c468 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((975871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -550301/10000000) (δ := 14519/1000000000) (ψ := -744563/1000000) 287 281
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t468 : ((1804200579/40000000000 : ℚ) : ℝ) ≤ stT287 468 := by
  have hc : ((975771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1804200579/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((975771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c469 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((923963/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490601/5000000) (δ := 3621/250000000) (ψ := -744563/1000000) 287 281
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t469 : ((426600207291/10000000000000 : ℚ) : ℝ) ≤ stT287 469 := by
  have hc : ((923863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426600207291/10000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((923863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c470 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((537133/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1254703/5000000) (δ := 14519/1000000000) (ψ := -744563/1000000) 287 281
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t470 : ((49542905349/2000000000000 : ℚ) : ℝ) ≤ stT287 470 := by
  have hc : ((537033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49542905349/2000000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((537033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c471 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-21471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201719/500000) (δ := 899/62500000) (ψ := -744563/1000000) 287 281
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t471 : ((-1239545037/625000000000 : ℚ) : ℝ) ≤ stT287 471 := by
  have hc : ((-21521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1239545037/625000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-21521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c472 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-303251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2778063/5000000) (δ := 14419/1000000000) (ψ := -744563/1000000) 287 281
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t472 : ((-272667599/9765625000 : ℚ) : ℝ) ≤ stT287 472 := by
  have hc : ((-303301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272667599/9765625000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-303301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c473 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-951803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7074643/10000000) (δ := 14419/1000000000) (ψ := -744563/1000000) 287 281
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t473 : ((-437685951303/10000000000000 : ℚ) : ℝ) ≤ stT287 473 := by
  have hc : ((-951903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437685951303/10000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-951903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c474 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-478487/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177949/250000) (δ := 7263/500000000) (ψ := -744563/1000000) 287 282
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t474 : ((-54949925173/1250000000000 : ℚ) : ℝ) ≤ stT287 474 := by
  have hc : ((-478537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54949925173/1250000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-478537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c475 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-622189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5605829/10000000) (δ := 7213/500000000) (ψ := -744563/1000000) 287 282
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t475 : ((-17845381653/625000000000 : ℚ) : ℝ) ≤ stT287 475 := by
  have hc : ((-622289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17845381653/625000000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-622289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c476 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-33961/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4096927/10000000) (δ := 14477/1000000000) (ψ := -744563/1000000) 287 282
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t476 : ((-311778837/100000000000 : ℚ) : ℝ) ≤ stT287 476 := by
  have hc : ((-34011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311778837/100000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-34011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c477 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((509259/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2591181/10000000) (δ := 7213/500000000) (ψ := -744563/1000000) 287 282
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t477 : ((58281903253/2500000000000 : ℚ) : ℝ) ≤ stT287 477 := by
  have hc : ((509159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58281903253/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((509159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c478 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((453349/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1088521/10000000) (δ := 14377/1000000000) (ψ := -744563/1000000) 287 282
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t478 : ((207333976311/5000000000000 : ℚ) : ℝ) ≤ stT287 478 := by
  have hc : ((453299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207333976311/5000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((453299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c479 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((986523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410911/10000000) (δ := 7263/500000000) (ψ := -744563/1000000) 287 282
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t479 : ((450707519353/10000000000000 : ℚ) : ℝ) ≤ stT287 479 := by
  have hc : ((986423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450707519353/10000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((986423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c480 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((722813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1907329/10000000) (δ := 7263/500000000) (ψ := -744563/1000000) 287 282
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t480 : ((65974301631/2000000000000 : ℚ) : ℝ) ≤ stT287 480 := by
  have hc : ((722713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65974301631/2000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((722713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c481 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((52259/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1700259/5000000) (δ := 7213/500000000) (ψ := -744563/1000000) 287 282
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t481 : ((297707683/31250000000 : ℚ) : ℝ) ≤ stT287 481 := by
  have hc : ((26117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297707683/31250000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((26117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c482 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-75201/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2445347/5000000) (δ := 7263/500000000) (ψ := -744563/1000000) 287 282
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t482 : ((-535347857/31250000000 : ℚ) : ℝ) ≤ stT287 482 := by
  have hc : ((-75221/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-535347857/31250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-75221/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c483 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-415329/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398607/625000) (δ := 14477/1000000000) (ψ := -744563/1000000) 287 282
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t483 : ((-23625511383/625000000000 : ℚ) : ℝ) ≤ stT287 483 := by
  have hc : ((-415379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23625511383/625000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-415379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c484 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-199999/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3923123/5000000) (δ := 1447/100000000) (ψ := -744563/1000000) 287 283
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t484 : ((-45458918187/1000000000000 : ℚ) : ℝ) ≤ stT287 484 := by
  have hc : ((-200019/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45458918187/1000000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-200019/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c485 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-165581/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6365397/10000000) (δ := 14533/1000000000) (ψ := -744563/1000000) 287 283
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t485 : ((-75195605277/2000000000000 : ℚ) : ℝ) ≤ stT287 485 := by
  have hc : ((-165601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75195605277/2000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-165601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c486 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-187409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4887491/10000000) (δ := 1437/100000000) (ψ := -744563/1000000) 287 283
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t486 : ((-8503327699/500000000000 : ℚ) : ℝ) ≤ stT287 486 := by
  have hc : ((-187459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8503327699/500000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-187459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c487 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((5107/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341267/1000000) (δ := 1447/100000000) (ψ := -744563/1000000) 287 283
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t487 : ((4626136887/500000000000 : ℚ) : ℝ) ≤ stT287 487 := by
  have hc : ((10209/50000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4626136887/500000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((10209/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c488 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((713479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -970431/5000000) (δ := 1437/100000000) (ψ := -744563/1000000) 287 283
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t488 : ((161465489481/5000000000000 : ℚ) : ℝ) ≤ stT287 488 := by
  have hc : ((713379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161465489481/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((713379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c489 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((49111/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -472139/10000000) (δ := 14533/1000000000) (ψ := -744563/1000000) 287 283
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t489 : ((2220646979/50000000000 : ℚ) : ℝ) ≤ stT287 489 := by
  have hc : ((24553/25000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2220646979/50000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((24553/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c490 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((922049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 993641/10000000) (δ := 1447/100000000) (ψ := -744563/1000000) 287 283
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t490 : ((416493226597/10000000000000 : ℚ) : ℝ) ≤ stT287 490 := by
  have hc : ((921949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416493226597/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((921949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c491 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((138717/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15353/62500) (δ := 1447/100000000) (ψ := -744563/1000000) 287 283
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t491 : ((15647682189/625000000000 : ℚ) : ℝ) ≤ stT287 491 := by
  have hc : ((34673/62500 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15647682189/625000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((34673/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c492 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((2137/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1958153/5000000) (δ := 14433/1000000000) (ψ := -744563/1000000) 287 283
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t492 : ((470445279/2500000000000 : ℚ) : ℝ) ≤ stT287 492 := by
  have hc : ((2087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((470445279/2500000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((2087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c493 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-546727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2686559/5000000) (δ := 14433/1000000000) (ψ := -744563/1000000) 287 283
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t493 : ((-123139425303/5000000000000 : ℚ) : ℝ) ≤ stT287 493 := by
  have hc : ((-546827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123139425303/5000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-546827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c494 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-458407/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341353/500000) (δ := 14433/1000000000) (ψ := -744563/1000000) 287 283
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t494 : ((-103134945177/2500000000000 : ℚ) : ℝ) ≤ stT287 494 := by
  have hc : ((-458457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103134945177/2500000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-458457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c495 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-246413/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297199/400000) (δ := 7181/500000000) (ψ := -744563/1000000) 287 284
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t495 : ((-55382874273/1250000000000 : ℚ) : ℝ) ≤ stT287 495 := by
  have hc : ((-123219/125000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55382874273/1250000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-123219/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c496 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-91561/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1495479/2500000) (δ := 14541/1000000000) (ψ := -744563/1000000) 287 284
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t496 : ((-41117783529/1250000000000 : ℚ) : ℝ) ≤ stT287 496 := by
  have hc : ((-183147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41117783529/1250000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-183147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c497 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-30189/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5671/12500) (δ := 7231/500000000) (ψ := -744563/1000000) 287 284
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t497 : ((-13547245243/1250000000000 : ℚ) : ℝ) ≤ stT287 497 := by
  have hc : ((-60403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13547245243/1250000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-60403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c498 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((326829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24757/80000) (δ := 7231/500000000) (ψ := -744563/1000000) 287 284
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t498 : ((14641053219/1000000000000 : ℚ) : ℝ) ≤ stT287 498 := by
  have hc : ((326729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14641053219/1000000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((326729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c499 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((394343/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41383/250000) (δ := 7231/500000000) (ψ := -744563/1000000) 287 284
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t499 : ((176509598673/5000000000000 : ℚ) : ℝ) ≤ stT287 499 := by
  have hc : ((394293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176509598673/5000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((394293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_c500 :
    |Real.cos (((287 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((99617/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43777/2000000) (δ := 7231/500000000) (ψ := -744563/1000000) 287 284
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st287_t500 : ((44545545291/1000000000000 : ℚ) : ℝ) ≤ stT287 500 := by
  have hc : ((99607/100000 : ℚ) : ℝ)
      ≤ Real.cos (((287 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st287_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44545545291/1000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((99607/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st287_p1 : ((183821/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT287 (i+1) := by
  rw [Finset.sum_range_one]
  exact st287_t1

theorem st287_p2 : ((8664374436093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT287 (i+1))
      = (∑ i ∈ Finset.range 1, stT287 (i+1)) + stT287 2 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 1
    simpa using h
  have hprev := st287_p1
  have hstep := st287_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p3 : ((3434196768687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT287 (i+1))
      = (∑ i ∈ Finset.range 2, stT287 (i+1)) + stT287 3 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 2
    simpa using h
  have hprev := st287_p2
  have hstep := st287_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p4 : ((220847260539/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT287 (i+1))
      = (∑ i ∈ Finset.range 3, stT287 (i+1)) + stT287 4 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 3
    simpa using h
  have hprev := st287_p3
  have hstep := st287_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p5 : ((-389919987381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT287 (i+1))
      = (∑ i ∈ Finset.range 4, stT287 (i+1)) + stT287 5 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 4
    simpa using h
  have hprev := st287_p4
  have hstep := st287_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p6 : ((1591798425059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT287 (i+1))
      = (∑ i ∈ Finset.range 5, stT287 (i+1)) + stT287 6 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 5
    simpa using h
  have hprev := st287_p5
  have hstep := st287_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p7 : ((3481149859381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT287 (i+1))
      = (∑ i ∈ Finset.range 6, stT287 (i+1)) + stT287 7 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 6
    simpa using h
  have hprev := st287_p6
  have hstep := st287_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p8 : ((9794222760899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT287 (i+1))
      = (∑ i ∈ Finset.range 7, stT287 (i+1)) + stT287 8 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 7
    simpa using h
  have hprev := st287_p7
  have hstep := st287_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p9 : ((6481482098351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT287 (i+1))
      = (∑ i ∈ Finset.range 8, stT287 (i+1)) + stT287 9 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 8
    simpa using h
  have hprev := st287_p8
  have hstep := st287_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p10 : ((1120709668809/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT287 (i+1))
      = (∑ i ∈ Finset.range 9, stT287 (i+1)) + stT287 10 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 9
    simpa using h
  have hprev := st287_p9
  have hstep := st287_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p11 : ((3804842890863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT287 (i+1))
      = (∑ i ∈ Finset.range 10, stT287 (i+1)) + stT287 11 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 10
    simpa using h
  have hprev := st287_p10
  have hstep := st287_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p12 : ((1734614467567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT287 (i+1))
      = (∑ i ∈ Finset.range 11, stT287 (i+1)) + stT287 12 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 11
    simpa using h
  have hprev := st287_p11
  have hstep := st287_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p13 : ((1233570417913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT287 (i+1))
      = (∑ i ∈ Finset.range 12, stT287 (i+1)) + stT287 13 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 12
    simpa using h
  have hprev := st287_p12
  have hstep := st287_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p14 : ((-35541285419/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT287 (i+1))
      = (∑ i ∈ Finset.range 13, stT287 (i+1)) + stT287 14 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 13
    simpa using h
  have hprev := st287_p13
  have hstep := st287_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p15 : ((222170809843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT287 (i+1))
      = (∑ i ∈ Finset.range 14, stT287 (i+1)) + stT287 15 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 14
    simpa using h
  have hprev := st287_p14
  have hstep := st287_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p16 : ((274420184843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT287 (i+1))
      = (∑ i ∈ Finset.range 15, stT287 (i+1)) + stT287 16 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 15
    simpa using h
  have hprev := st287_p15
  have hstep := st287_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p17 : ((-319370268039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT287 (i+1))
      = (∑ i ∈ Finset.range 16, stT287 (i+1)) + stT287 17 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 16
    simpa using h
  have hprev := st287_p16
  have hstep := st287_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p18 : ((92981623179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT287 (i+1))
      = (∑ i ∈ Finset.range 17, stT287 (i+1)) + stT287 18 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 17
    simpa using h
  have hprev := st287_p17
  have hstep := st287_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p19 : ((-194236471059/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT287 (i+1))
      = (∑ i ∈ Finset.range 18, stT287 (i+1)) + stT287 19 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 18
    simpa using h
  have hprev := st287_p18
  have hstep := st287_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p20 : ((119383246577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT287 (i+1))
      = (∑ i ∈ Finset.range 19, stT287 (i+1)) + stT287 20 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 19
    simpa using h
  have hprev := st287_p19
  have hstep := st287_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p21 : ((293726175709/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT287 (i+1))
      = (∑ i ∈ Finset.range 20, stT287 (i+1)) + stT287 21 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 20
    simpa using h
  have hprev := st287_p20
  have hstep := st287_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p22 : ((689859524337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT287 (i+1))
      = (∑ i ∈ Finset.range 21, stT287 (i+1)) + stT287 22 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 21
    simpa using h
  have hprev := st287_p21
  have hstep := st287_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p23 : ((-213487707419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT287 (i+1))
      = (∑ i ∈ Finset.range 22, stT287 (i+1)) + stT287 23 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 22
    simpa using h
  have hprev := st287_p22
  have hstep := st287_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p24 : ((-107423249549/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT287 (i+1))
      = (∑ i ∈ Finset.range 23, stT287 (i+1)) + stT287 24 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 23
    simpa using h
  have hprev := st287_p23
  have hstep := st287_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p25 : ((41269500451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT287 (i+1))
      = (∑ i ∈ Finset.range 24, stT287 (i+1)) + stT287 25 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 24
    simpa using h
  have hprev := st287_p24
  have hstep := st287_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p26 : ((430774591449/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT287 (i+1))
      = (∑ i ∈ Finset.range 25, stT287 (i+1)) + stT287 26 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 25
    simpa using h
  have hprev := st287_p25
  have hstep := st287_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p27 : ((581744088563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT287 (i+1))
      = (∑ i ∈ Finset.range 26, stT287 (i+1)) + stT287 27 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 26
    simpa using h
  have hprev := st287_p26
  have hstep := st287_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p28 : ((303541229383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT287 (i+1))
      = (∑ i ∈ Finset.range 27, stT287 (i+1)) + stT287 28 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 27
    simpa using h
  have hprev := st287_p27
  have hstep := st287_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p29 : ((986886017187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT287 (i+1))
      = (∑ i ∈ Finset.range 28, stT287 (i+1)) + stT287 29 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 28
    simpa using h
  have hprev := st287_p28
  have hstep := st287_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p30 : ((83784562629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT287 (i+1))
      = (∑ i ∈ Finset.range 29, stT287 (i+1)) + stT287 30 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 29
    simpa using h
  have hprev := st287_p29
  have hstep := st287_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p31 : ((1940160284919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT287 (i+1))
      = (∑ i ∈ Finset.range 30, stT287 (i+1)) + stT287 31 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 30
    simpa using h
  have hprev := st287_p30
  have hstep := st287_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p32 : ((367187066183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT287 (i+1))
      = (∑ i ∈ Finset.range 31, stT287 (i+1)) + stT287 32 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 31
    simpa using h
  have hprev := st287_p31
  have hstep := st287_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p33 : ((241348140179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT287 (i+1))
      = (∑ i ∈ Finset.range 32, stT287 (i+1)) + stT287 33 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 32
    simpa using h
  have hprev := st287_p32
  have hstep := st287_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p34 : ((14403309027/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT287 (i+1))
      = (∑ i ∈ Finset.range 33, stT287 (i+1)) + stT287 34 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 33
    simpa using h
  have hprev := st287_p33
  have hstep := st287_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p35 : ((120496648107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT287 (i+1))
      = (∑ i ∈ Finset.range 34, stT287 (i+1)) + stT287 35 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 34
    simpa using h
  have hprev := st287_p34
  have hstep := st287_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p36 : ((680708090689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT287 (i+1))
      = (∑ i ∈ Finset.range 35, stT287 (i+1)) + stT287 36 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 35
    simpa using h
  have hprev := st287_p35
  have hstep := st287_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p37 : ((444696652783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT287 (i+1))
      = (∑ i ∈ Finset.range 36, stT287 (i+1)) + stT287 37 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 36
    simpa using h
  have hprev := st287_p36
  have hstep := st287_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p38 : ((395464374191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT287 (i+1))
      = (∑ i ∈ Finset.range 37, stT287 (i+1)) + stT287 38 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 37
    simpa using h
  have hprev := st287_p37
  have hstep := st287_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p39 : ((424393783509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT287 (i+1))
      = (∑ i ∈ Finset.range 38, stT287 (i+1)) + stT287 39 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 38
    simpa using h
  have hprev := st287_p38
  have hstep := st287_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p40 : ((-747385167113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT287 (i+1))
      = (∑ i ∈ Finset.range 39, stT287 (i+1)) + stT287 40 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 39
    simpa using h
  have hprev := st287_p39
  have hstep := st287_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p41 : ((-795892749393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT287 (i+1))
      = (∑ i ∈ Finset.range 40, stT287 (i+1)) + stT287 41 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 40
    simpa using h
  have hprev := st287_p40
  have hstep := st287_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p42 : ((77584285181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT287 (i+1))
      = (∑ i ∈ Finset.range 41, stT287 (i+1)) + stT287 42 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 41
    simpa using h
  have hprev := st287_p41
  have hstep := st287_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p43 : ((708279619903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT287 (i+1))
      = (∑ i ∈ Finset.range 42, stT287 (i+1)) + stT287 43 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 42
    simpa using h
  have hprev := st287_p42
  have hstep := st287_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p44 : ((1449249424127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT287 (i+1))
      = (∑ i ∈ Finset.range 43, stT287 (i+1)) + stT287 44 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 43
    simpa using h
  have hprev := st287_p43
  have hstep := st287_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p45 : ((219441560383/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT287 (i+1))
      = (∑ i ∈ Finset.range 44, stT287 (i+1)) + stT287 45 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 44
    simpa using h
  have hprev := st287_p44
  have hstep := st287_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p46 : ((2931532215433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT287 (i+1))
      = (∑ i ∈ Finset.range 45, stT287 (i+1)) + stT287 46 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 45
    simpa using h
  have hprev := st287_p45
  have hstep := st287_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p47 : ((1828433655209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT287 (i+1))
      = (∑ i ∈ Finset.range 46, stT287 (i+1)) + stT287 47 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 46
    simpa using h
  have hprev := st287_p46
  have hstep := st287_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p48 : ((8672142464711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT287 (i+1))
      = (∑ i ∈ Finset.range 47, stT287 (i+1)) + stT287 48 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 47
    simpa using h
  have hprev := st287_p47
  have hstep := st287_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p49 : ((2438840892079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT287 (i+1))
      = (∑ i ∈ Finset.range 48, stT287 (i+1)) + stT287 49 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 48
    simpa using h
  have hprev := st287_p48
  have hstep := st287_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p50 : ((10274268016489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT287 (i+1))
      = (∑ i ∈ Finset.range 49, stT287 (i+1)) + stT287 50 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 49
    simpa using h
  have hprev := st287_p49
  have hstep := st287_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p51 : ((1245379320003/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT287 (i+1))
      = (∑ i ∈ Finset.range 50, stT287 (i+1)) + stT287 51 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 50
    simpa using h
  have hprev := st287_p50
  have hstep := st287_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p52 : ((1769551064507/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT287 (i+1))
      = (∑ i ∈ Finset.range 51, stT287 (i+1)) + stT287 52 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 51
    simpa using h
  have hprev := st287_p51
  have hstep := st287_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p53 : ((7496150369837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT287 (i+1))
      = (∑ i ∈ Finset.range 52, stT287 (i+1)) + stT287 53 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 52
    simpa using h
  have hprev := st287_p52
  have hstep := st287_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p54 : ((6876727319969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT287 (i+1))
      = (∑ i ∈ Finset.range 53, stT287 (i+1)) + stT287 54 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 53
    simpa using h
  have hprev := st287_p53
  have hstep := st287_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p55 : ((7575084736453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT287 (i+1))
      = (∑ i ∈ Finset.range 54, stT287 (i+1)) + stT287 55 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 54
    simpa using h
  have hprev := st287_p54
  have hstep := st287_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p56 : ((8906363553281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT287 (i+1))
      = (∑ i ∈ Finset.range 55, stT287 (i+1)) + stT287 56 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 55
    simpa using h
  have hprev := st287_p55
  have hstep := st287_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p57 : ((1854909272477/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT287 (i+1))
      = (∑ i ∈ Finset.range 56, stT287 (i+1)) + stT287 57 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 56
    simpa using h
  have hprev := st287_p56
  have hstep := st287_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p58 : ((816250242243/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT287 (i+1))
      = (∑ i ∈ Finset.range 57, stT287 (i+1)) + stT287 58 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 57
    simpa using h
  have hprev := st287_p57
  have hstep := st287_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p59 : ((181765774023/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT287 (i+1))
      = (∑ i ∈ Finset.range 58, stT287 (i+1)) + stT287 59 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 58
    simpa using h
  have hprev := st287_p58
  have hstep := st287_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p60 : ((2026777466829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT287 (i+1))
      = (∑ i ∈ Finset.range 59, stT287 (i+1)) + stT287 60 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 59
    simpa using h
  have hprev := st287_p59
  have hstep := st287_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p61 : ((2276947289981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT287 (i+1))
      = (∑ i ∈ Finset.range 60, stT287 (i+1)) + stT287 61 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 60
    simpa using h
  have hprev := st287_p60
  have hstep := st287_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p62 : ((82710966023/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT287 (i+1))
      = (∑ i ∈ Finset.range 61, stT287 (i+1)) + stT287 62 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 61
    simpa using h
  have hprev := st287_p61
  have hstep := st287_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p63 : ((29717855717/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT287 (i+1))
      = (∑ i ∈ Finset.range 62, stT287 (i+1)) + stT287 63 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 62
    simpa using h
  have hprev := st287_p62
  have hstep := st287_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p64 : ((34009005717/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT287 (i+1))
      = (∑ i ∈ Finset.range 63, stT287 (i+1)) + stT287 64 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 63
    simpa using h
  have hprev := st287_p63
  have hstep := st287_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p65 : ((4420130435457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT287 (i+1))
      = (∑ i ∈ Finset.range 64, stT287 (i+1)) + stT287 65 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 64
    simpa using h
  have hprev := st287_p64
  have hstep := st287_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p66 : ((7611050688189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT287 (i+1))
      = (∑ i ∈ Finset.range 65, stT287 (i+1)) + stT287 66 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 65
    simpa using h
  have hprev := st287_p65
  have hstep := st287_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p67 : ((8143446607979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT287 (i+1))
      = (∑ i ∈ Finset.range 66, stT287 (i+1)) + stT287 67 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 66
    simpa using h
  have hprev := st287_p66
  have hstep := st287_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p68 : ((8886186416741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT287 (i+1))
      = (∑ i ∈ Finset.range 67, stT287 (i+1)) + stT287 68 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 67
    simpa using h
  have hprev := st287_p67
  have hstep := st287_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p69 : ((751313699/976562500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT287 (i+1))
      = (∑ i ∈ Finset.range 68, stT287 (i+1)) + stT287 69 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 68
    simpa using h
  have hprev := st287_p68
  have hstep := st287_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p70 : ((1026119563077/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT287 (i+1))
      = (∑ i ∈ Finset.range 69, stT287 (i+1)) + stT287 70 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 69
    simpa using h
  have hprev := st287_p69
  have hstep := st287_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p71 : ((8760383615237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT287 (i+1))
      = (∑ i ∈ Finset.range 70, stT287 (i+1)) + stT287 71 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 70
    simpa using h
  have hprev := st287_p70
  have hstep := st287_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p72 : ((1521776386353/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT287 (i+1))
      = (∑ i ∈ Finset.range 71, stT287 (i+1)) + stT287 72 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 71
    simpa using h
  have hprev := st287_p71
  have hstep := st287_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p73 : ((428667663213/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT287 (i+1))
      = (∑ i ∈ Finset.range 72, stT287 (i+1)) + stT287 73 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 72
    simpa using h
  have hprev := st287_p72
  have hstep := st287_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p74 : ((4168026092171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT287 (i+1))
      = (∑ i ∈ Finset.range 73, stT287 (i+1)) + stT287 74 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 73
    simpa using h
  have hprev := st287_p73
  have hstep := st287_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p75 : ((7776919402019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT287 (i+1))
      = (∑ i ∈ Finset.range 74, stT287 (i+1)) + stT287 75 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 74
    simpa using h
  have hprev := st287_p74
  have hstep := st287_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p76 : ((8830790432051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT287 (i+1))
      = (∑ i ∈ Finset.range 75, stT287 (i+1)) + stT287 76 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 75
    simpa using h
  have hprev := st287_p75
  have hstep := st287_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p77 : ((7714803906007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT287 (i+1))
      = (∑ i ∈ Finset.range 76, stT287 (i+1)) + stT287 77 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 76
    simpa using h
  have hprev := st287_p76
  have hstep := st287_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p78 : ((8530611749061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT287 (i+1))
      = (∑ i ∈ Finset.range 77, stT287 (i+1)) + stT287 78 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 77
    simpa using h
  have hprev := st287_p77
  have hstep := st287_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p79 : ((8208595812229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT287 (i+1))
      = (∑ i ∈ Finset.range 78, stT287 (i+1)) + stT287 79 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 78
    simpa using h
  have hprev := st287_p78
  have hstep := st287_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p80 : ((8010133596889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT287 (i+1))
      = (∑ i ∈ Finset.range 79, stT287 (i+1)) + stT287 80 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 79
    simpa using h
  have hprev := st287_p79
  have hstep := st287_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p81 : ((4319626211433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT287 (i+1))
      = (∑ i ∈ Finset.range 80, stT287 (i+1)) + stT287 81 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 80
    simpa using h
  have hprev := st287_p80
  have hstep := st287_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p82 : ((3860407998151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT287 (i+1))
      = (∑ i ∈ Finset.range 81, stT287 (i+1)) + stT287 82 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 81
    simpa using h
  have hprev := st287_p81
  have hstep := st287_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p83 : ((2195947243433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT287 (i+1))
      = (∑ i ∈ Finset.range 82, stT287 (i+1)) + stT287 83 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 82
    simpa using h
  have hprev := st287_p82
  have hstep := st287_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p84 : ((961705482209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT287 (i+1))
      = (∑ i ∈ Finset.range 83, stT287 (i+1)) + stT287 84 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 83
    simpa using h
  have hprev := st287_p83
  have hstep := st287_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p85 : ((109126363849/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT287 (i+1))
      = (∑ i ∈ Finset.range 84, stT287 (i+1)) + stT287 85 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 84
    simpa using h
  have hprev := st287_p84
  have hstep := st287_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p86 : ((121734640249/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT287 (i+1))
      = (∑ i ∈ Finset.range 85, stT287 (i+1)) + stT287 86 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 85
    simpa using h
  have hprev := st287_p85
  have hstep := st287_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p87 : ((13464843031/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT287 (i+1))
      = (∑ i ∈ Finset.range 86, stT287 (i+1)) + stT287 87 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 86
    simpa using h
  have hprev := st287_p86
  have hstep := st287_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p88 : ((1974265780631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT287 (i+1))
      = (∑ i ∈ Finset.range 87, stT287 (i+1)) + stT287 88 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 87
    simpa using h
  have hprev := st287_p87
  have hstep := st287_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p89 : ((426524170491/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT287 (i+1))
      = (∑ i ∈ Finset.range 88, stT287 (i+1)) + stT287 89 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 88
    simpa using h
  have hprev := st287_p88
  have hstep := st287_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p90 : ((994591519647/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT287 (i+1))
      = (∑ i ∈ Finset.range 89, stT287 (i+1)) + stT287 90 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 89
    simpa using h
  have hprev := st287_p89
  have hstep := st287_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p91 : ((132823918011/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT287 (i+1))
      = (∑ i ∈ Finset.range 90, stT287 (i+1)) + stT287 91 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 90
    simpa using h
  have hprev := st287_p90
  have hstep := st287_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p92 : ((7955078279121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT287 (i+1))
      = (∑ i ∈ Finset.range 91, stT287 (i+1)) + stT287 92 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 91
    simpa using h
  have hprev := st287_p91
  have hstep := st287_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p93 : ((4265752929829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT287 (i+1))
      = (∑ i ∈ Finset.range 92, stT287 (i+1)) + stT287 93 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 92
    simpa using h
  have hprev := st287_p92
  have hstep := st287_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p94 : ((1974431222263/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT287 (i+1))
      = (∑ i ∈ Finset.range 93, stT287 (i+1)) + stT287 94 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 93
    simpa using h
  have hprev := st287_p93
  have hstep := st287_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p95 : ((4304489503831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT287 (i+1))
      = (∑ i ∈ Finset.range 94, stT287 (i+1)) + stT287 95 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 94
    simpa using h
  have hprev := st287_p94
  have hstep := st287_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p96 : ((3903922297477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT287 (i+1))
      = (∑ i ∈ Finset.range 95, stT287 (i+1)) + stT287 96 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 95
    simpa using h
  have hprev := st287_p95
  have hstep := st287_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p97 : ((4349182994203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT287 (i+1))
      = (∑ i ∈ Finset.range 96, stT287 (i+1)) + stT287 97 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 96
    simpa using h
  have hprev := st287_p96
  have hstep := st287_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p98 : ((3867049089139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT287 (i+1))
      = (∑ i ∈ Finset.range 97, stT287 (i+1)) + stT287 98 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 97
    simpa using h
  have hprev := st287_p97
  have hstep := st287_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p99 : ((8736205495423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT287 (i+1))
      = (∑ i ∈ Finset.range 98, stT287 (i+1)) + stT287 99 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 98
    simpa using h
  have hprev := st287_p98
  have hstep := st287_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p100 : ((7752641495423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT287 (i+1))
      = (∑ i ∈ Finset.range 99, stT287 (i+1)) + stT287 100 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 99
    simpa using h
  have hprev := st287_p99
  have hstep := st287_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p101 : ((8640612514223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT287 (i+1))
      = (∑ i ∈ Finset.range 100, stT287 (i+1)) + stT287 101 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 100
    simpa using h
  have hprev := st287_p100
  have hstep := st287_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p102 : ((1587588618879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT287 (i+1))
      = (∑ i ∈ Finset.range 101, stT287 (i+1)) + stT287 102 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 101
    simpa using h
  have hprev := st287_p101
  have hstep := st287_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p103 : ((2091004026147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT287 (i+1))
      = (∑ i ∈ Finset.range 102, stT287 (i+1)) + stT287 103 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 102
    simpa using h
  have hprev := st287_p102
  have hstep := st287_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p104 : ((8286868894413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT287 (i+1))
      = (∑ i ∈ Finset.range 103, stT287 (i+1)) + stT287 104 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 103
    simpa using h
  have hprev := st287_p103
  have hstep := st287_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p105 : ((399151935419/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT287 (i+1))
      = (∑ i ∈ Finset.range 104, stT287 (i+1)) + stT287 105 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 104
    simpa using h
  have hprev := st287_p104
  have hstep := st287_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p106 : ((1727242660321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT287 (i+1))
      = (∑ i ∈ Finset.range 105, stT287 (i+1)) + stT287 106 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 105
    simpa using h
  have hprev := st287_p105
  have hstep := st287_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p107 : ((3870324223141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT287 (i+1))
      = (∑ i ∈ Finset.range 106, stT287 (i+1)) + stT287 107 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 106
    simpa using h
  have hprev := st287_p106
  have hstep := st287_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p108 : ((4349646928891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT287 (i+1))
      = (∑ i ∈ Finset.range 107, stT287 (i+1)) + stT287 108 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 107
    simpa using h
  have hprev := st287_p107
  have hstep := st287_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p109 : ((197474633481/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT287 (i+1))
      = (∑ i ∈ Finset.range 108, stT287 (i+1)) + stT287 109 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 108
    simpa using h
  have hprev := st287_p108
  have hstep := st287_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p110 : ((104116510979/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT287 (i+1))
      = (∑ i ∈ Finset.range 109, stT287 (i+1)) + stT287 110 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 109
    simpa using h
  have hprev := st287_p109
  have hstep := st287_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p111 : ((210029776159/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT287 (i+1))
      = (∑ i ∈ Finset.range 110, stT287 (i+1)) + stT287 111 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 110
    simpa using h
  have hprev := st287_p110
  have hstep := st287_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p112 : ((979269023737/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT287 (i+1))
      = (∑ i ∈ Finset.range 111, stT287 (i+1)) + stT287 112 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 111
    simpa using h
  have hprev := st287_p111
  have hstep := st287_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p113 : ((1090238824327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT287 (i+1))
      = (∑ i ∈ Finset.range 112, stT287 (i+1)) + stT287 113 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 112
    simpa using h
  have hprev := st287_p112
  have hstep := st287_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p114 : ((391035159709/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT287 (i+1))
      = (∑ i ∈ Finset.range 113, stT287 (i+1)) + stT287 114 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 113
    simpa using h
  have hprev := st287_p113
  have hstep := st287_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p115 : ((419605217261/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT287 (i+1))
      = (∑ i ∈ Finset.range 114, stT287 (i+1)) + stT287 115 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 114
    simpa using h
  have hprev := st287_p114
  have hstep := st287_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p116 : ((65541350913/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT287 (i+1))
      = (∑ i ∈ Finset.range 115, stT287 (i+1)) + stT287 116 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 115
    simpa using h
  have hprev := st287_p115
  have hstep := st287_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p117 : ((3905700142389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT287 (i+1))
      = (∑ i ∈ Finset.range 116, stT287 (i+1)) + stT287 117 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 116
    simpa using h
  have hprev := st287_p116
  have hstep := st287_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p118 : ((1089267270441/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT287 (i+1))
      = (∑ i ∈ Finset.range 117, stT287 (i+1)) + stT287 118 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 117
    simpa using h
  have hprev := st287_p117
  have hstep := st287_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p119 : ((3959943157877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT287 (i+1))
      = (∑ i ∈ Finset.range 118, stT287 (i+1)) + stT287 119 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 118
    simpa using h
  have hprev := st287_p118
  have hstep := st287_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p120 : ((2049113950261/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT287 (i+1))
      = (∑ i ∈ Finset.range 119, stT287 (i+1)) + stT287 120 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 119
    simpa using h
  have hprev := st287_p119
  have hstep := st287_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p121 : ((4296682702067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT287 (i+1))
      = (∑ i ∈ Finset.range 120, stT287 (i+1)) + stT287 121 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 120
    simpa using h
  have hprev := st287_p120
  have hstep := st287_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p122 : ((241861627157/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT287 (i+1))
      = (∑ i ∈ Finset.range 121, stT287 (i+1)) + stT287 122 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 121
    simpa using h
  have hprev := st287_p121
  have hstep := st287_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p123 : ((8547706435309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT287 (i+1))
      = (∑ i ∈ Finset.range 122, stT287 (i+1)) + stT287 123 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 122
    simpa using h
  have hprev := st287_p122
  have hstep := st287_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p124 : ((1035944062943/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT287 (i+1))
      = (∑ i ∈ Finset.range 123, stT287 (i+1)) + stT287 124 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 123
    simpa using h
  have hprev := st287_p123
  have hstep := st287_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p125 : ((1956413222553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT287 (i+1))
      = (∑ i ∈ Finset.range 124, stT287 (i+1)) + stT287 125 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 124
    simpa using h
  have hprev := st287_p124
  have hstep := st287_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p126 : ((4351526913341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT287 (i+1))
      = (∑ i ∈ Finset.range 125, stT287 (i+1)) + stT287 126 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 125
    simpa using h
  have hprev := st287_p125
  have hstep := st287_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p127 : ((501492256439/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT287 (i+1))
      = (∑ i ∈ Finset.range 126, stT287 (i+1)) + stT287 127 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 126
    simpa using h
  have hprev := st287_p126
  have hstep := st287_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p128 : ((50043181661/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT287 (i+1))
      = (∑ i ∈ Finset.range 127, stT287 (i+1)) + stT287 128 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 127
    simpa using h
  have hprev := st287_p127
  have hstep := st287_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p129 : ((435556497733/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT287 (i+1))
      = (∑ i ∈ Finset.range 128, stT287 (i+1)) + stT287 129 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 128
    simpa using h
  have hprev := st287_p128
  have hstep := st287_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p130 : ((3934286350801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT287 (i+1))
      = (∑ i ∈ Finset.range 129, stT287 (i+1)) + stT287 130 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 129
    simpa using h
  have hprev := st287_p129
  have hstep := st287_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p131 : ((4082673180197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT287 (i+1))
      = (∑ i ∈ Finset.range 130, stT287 (i+1)) + stT287 131 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 130
    simpa using h
  have hprev := st287_p130
  have hstep := st287_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p132 : ((4332792663011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT287 (i+1))
      = (∑ i ∈ Finset.range 131, stT287 (i+1)) + stT287 132 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 131
    simpa using h
  have hprev := st287_p131
  have hstep := st287_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p133 : ((121851813753/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT287 (i+1))
      = (∑ i ∈ Finset.range 132, stT287 (i+1)) + stT287 133 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 132
    simpa using h
  have hprev := st287_p132
  have hstep := st287_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p134 : ((129041787117/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT287 (i+1))
      = (∑ i ∈ Finset.range 133, stT287 (i+1)) + stT287 134 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 133
    simpa using h
  have hprev := st287_p133
  have hstep := st287_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p135 : ((539359837713/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT287 (i+1))
      = (∑ i ∈ Finset.range 134, stT287 (i+1)) + stT287 135 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 134
    simpa using h
  have hprev := st287_p134
  have hstep := st287_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p136 : ((7776583595649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT287 (i+1))
      = (∑ i ∈ Finset.range 135, stT287 (i+1)) + stT287 136 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 135
    simpa using h
  have hprev := st287_p135
  have hstep := st287_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p137 : ((8282043410131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT287 (i+1))
      = (∑ i ∈ Finset.range 136, stT287 (i+1)) + stT287 137 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 136
    simpa using h
  have hprev := st287_p136
  have hstep := st287_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p138 : ((8629944927283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT287 (i+1))
      = (∑ i ∈ Finset.range 137, stT287 (i+1)) + stT287 138 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 137
    simpa using h
  have hprev := st287_p137
  have hstep := st287_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p139 : ((7784403973341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT287 (i+1))
      = (∑ i ∈ Finset.range 138, stT287 (i+1)) + stT287 139 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 138
    simpa using h
  have hprev := st287_p138
  have hstep := st287_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p140 : ((8238157014093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT287 (i+1))
      = (∑ i ∈ Finset.range 139, stT287 (i+1)) + stT287 140 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 139
    simpa using h
  have hprev := st287_p139
  have hstep := st287_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p141 : ((270790210551/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT287 (i+1))
      = (∑ i ∈ Finset.range 140, stT287 (i+1)) + stT287 141 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 140
    simpa using h
  have hprev := st287_p140
  have hstep := st287_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p142 : ((3914175613923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT287 (i+1))
      = (∑ i ∈ Finset.range 141, stT287 (i+1)) + stT287 142 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 141
    simpa using h
  have hprev := st287_p141
  have hstep := st287_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p143 : ((162593185107/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT287 (i+1))
      = (∑ i ∈ Finset.range 142, stT287 (i+1)) + stT287 143 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 142
    simpa using h
  have hprev := st287_p142
  have hstep := st287_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p144 : ((8711418189313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT287 (i+1))
      = (∑ i ∈ Finset.range 143, stT287 (i+1)) + stT287 144 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 143
    simpa using h
  have hprev := st287_p143
  have hstep := st287_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p145 : ((7933388152553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT287 (i+1))
      = (∑ i ∈ Finset.range 144, stT287 (i+1)) + stT287 145 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 144
    simpa using h
  have hprev := st287_p144
  have hstep := st287_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p146 : ((7969888843473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT287 (i+1))
      = (∑ i ∈ Finset.range 145, stT287 (i+1)) + stT287 146 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 145
    simpa using h
  have hprev := st287_p145
  have hstep := st287_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p147 : ((8718662565713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT287 (i+1))
      = (∑ i ∈ Finset.range 146, stT287 (i+1)) + stT287 147 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 146
    simpa using h
  have hprev := st287_p146
  have hstep := st287_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p148 : ((8124677470783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT287 (i+1))
      = (∑ i ∈ Finset.range 147, stT287 (i+1)) + stT287 148 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 147
    simpa using h
  have hprev := st287_p147
  have hstep := st287_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p149 : ((7804460162783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT287 (i+1))
      = (∑ i ∈ Finset.range 148, stT287 (i+1)) + stT287 149 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 148
    simpa using h
  have hprev := st287_p148
  have hstep := st287_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p150 : ((8619746932207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT287 (i+1))
      = (∑ i ∈ Finset.range 149, stT287 (i+1)) + stT287 150 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 149
    simpa using h
  have hprev := st287_p149
  have hstep := st287_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p151 : ((8391918563767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT287 (i+1))
      = (∑ i ∈ Finset.range 150, stT287 (i+1)) + stT287 151 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 150
    simpa using h
  have hprev := st287_p150
  have hstep := st287_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p152 : ((1545148030463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT287 (i+1))
      = (∑ i ∈ Finset.range 151, stT287 (i+1)) + stT287 152 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 151
    simpa using h
  have hprev := st287_p151
  have hstep := st287_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p153 : ((1673619137783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT287 (i+1))
      = (∑ i ∈ Finset.range 152, stT287 (i+1)) + stT287 153 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 152
    simpa using h
  have hprev := st287_p152
  have hstep := st287_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p154 : ((8646935081397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT287 (i+1))
      = (∑ i ∈ Finset.range 153, stT287 (i+1)) + stT287 154 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 153
    simpa using h
  have hprev := st287_p153
  have hstep := st287_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p155 : ((7845417104577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT287 (i+1))
      = (∑ i ∈ Finset.range 154, stT287 (i+1)) + stT287 155 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 154
    simpa using h
  have hprev := st287_p154
  have hstep := st287_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p156 : ((8010859752897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT287 (i+1))
      = (∑ i ∈ Finset.range 155, stT287 (i+1)) + stT287 156 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 155
    simpa using h
  have hprev := st287_p155
  have hstep := st287_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p157 : ((8721852223889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT287 (i+1))
      = (∑ i ∈ Finset.range 156, stT287 (i+1)) + stT287 157 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 156
    simpa using h
  have hprev := st287_p156
  have hstep := st287_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p158 : ((8195557193453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT287 (i+1))
      = (∑ i ∈ Finset.range 157, stT287 (i+1)) + stT287 158 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 157
    simpa using h
  have hprev := st287_p157
  have hstep := st287_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p159 : ((1548478442533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT287 (i+1))
      = (∑ i ∈ Finset.range 158, stT287 (i+1)) + stT287 159 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 158
    simpa using h
  have hprev := st287_p158
  have hstep := st287_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p160 : ((8476623684587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT287 (i+1))
      = (∑ i ∈ Finset.range 159, stT287 (i+1)) + stT287 160 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 159
    simpa using h
  have hprev := st287_p159
  have hstep := st287_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p161 : ((8603797842847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT287 (i+1))
      = (∑ i ∈ Finset.range 160, stT287 (i+1)) + stT287 161 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 160
    simpa using h
  have hprev := st287_p160
  have hstep := st287_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p162 : ((7818809522797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT287 (i+1))
      = (∑ i ∈ Finset.range 161, stT287 (i+1)) + stT287 162 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 161
    simpa using h
  have hprev := st287_p161
  have hstep := st287_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p163 : ((8004536917257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT287 (i+1))
      = (∑ i ∈ Finset.range 162, stT287 (i+1)) + stT287 163 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 162
    simpa using h
  have hprev := st287_p162
  have hstep := st287_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p164 : ((8716163009093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT287 (i+1))
      = (∑ i ∈ Finset.range 163, stT287 (i+1)) + stT287 164 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 163
    simpa using h
  have hprev := st287_p163
  have hstep := st287_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p165 : ((8277840046129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT287 (i+1))
      = (∑ i ∈ Finset.range 164, stT287 (i+1)) + stT287 165 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 164
    simpa using h
  have hprev := st287_p164
  have hstep := st287_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p166 : ((241120751057/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT287 (i+1))
      = (∑ i ∈ Finset.range 165, stT287 (i+1)) + stT287 166 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 165
    simpa using h
  have hprev := st287_p165
  have hstep := st287_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p167 : ((4164363603443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT287 (i+1))
      = (∑ i ∈ Finset.range 166, stT287 (i+1)) + stT287 167 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 166
    simpa using h
  have hprev := st287_p166
  have hstep := st287_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p168 : ((4353968675297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT287 (i+1))
      = (∑ i ∈ Finset.range 167, stT287 (i+1)) + stT287 168 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 167
    simpa using h
  have hprev := st287_p167
  have hstep := st287_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p169 : ((1998479284097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT287 (i+1))
      = (∑ i ∈ Finset.range 168, stT287 (i+1)) + stT287 169 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 168
    simpa using h
  have hprev := st287_p168
  have hstep := st287_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p170 : ((3898692711499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT287 (i+1))
      = (∑ i ∈ Finset.range 169, stT287 (i+1)) + stT287 170 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 169
    simpa using h
  have hprev := st287_p169
  have hstep := st287_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p171 : ((8553830928137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT287 (i+1))
      = (∑ i ∈ Finset.range 170, stT287 (i+1)) + stT287 171 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 170
    simpa using h
  have hprev := st287_p170
  have hstep := st287_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p172 : ((1717439363113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT287 (i+1))
      = (∑ i ∈ Finset.range 171, stT287 (i+1)) + stT287 172 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 171
    simpa using h
  have hprev := st287_p171
  have hstep := st287_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p173 : ((1565550186319/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT287 (i+1))
      = (∑ i ∈ Finset.range 172, stT287 (i+1)) + stT287 173 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 172
    simpa using h
  have hprev := st287_p172
  have hstep := st287_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p174 : ((7927816835203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT287 (i+1))
      = (∑ i ∈ Finset.range 173, stT287 (i+1)) + stT287 174 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 173
    simpa using h
  have hprev := st287_p173
  have hstep := st287_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p175 : ((8667624670603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT287 (i+1))
      = (∑ i ∈ Finset.range 174, stT287 (i+1)) + stT287 175 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 174
    simpa using h
  have hprev := st287_p174
  have hstep := st287_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p176 : ((2116454796957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT287 (i+1))
      = (∑ i ∈ Finset.range 175, stT287 (i+1)) + stT287 176 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 175
    simpa using h
  have hprev := st287_p175
  have hstep := st287_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p177 : ((3876868691307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT287 (i+1))
      = (∑ i ∈ Finset.range 176, stT287 (i+1)) + stT287 177 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 176
    simpa using h
  have hprev := st287_p176
  have hstep := st287_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p178 : ((3919104159/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT287 (i+1))
      = (∑ i ∈ Finset.range 177, stT287 (i+1)) + stT287 178 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 177
    simpa using h
  have hprev := st287_p177
  have hstep := st287_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p179 : ((4355961015171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT287 (i+1))
      = (∑ i ∈ Finset.range 178, stT287 (i+1)) + stT287 179 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 178
    simpa using h
  have hprev := st287_p178
  have hstep := st287_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p180 : ((4198040948739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT287 (i+1))
      = (∑ i ∈ Finset.range 179, stT287 (i+1)) + stT287 180 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 179
    simpa using h
  have hprev := st287_p179
  have hstep := st287_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p181 : ((483055804533/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT287 (i+1))
      = (∑ i ∈ Finset.range 180, stT287 (i+1)) + stT287 181 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 180
    simpa using h
  have hprev := st287_p180
  have hstep := st287_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p182 : ((8062645423521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT287 (i+1))
      = (∑ i ∈ Finset.range 181, stT287 (i+1)) + stT287 182 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 181
    simpa using h
  have hprev := st287_p181
  have hstep := st287_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p183 : ((8721977331609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT287 (i+1))
      = (∑ i ∈ Finset.range 182, stT287 (i+1)) + stT287 183 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 182
    simpa using h
  have hprev := st287_p182
  have hstep := st287_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p184 : ((8393152183209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT287 (i+1))
      = (∑ i ∈ Finset.range 183, stT287 (i+1)) + stT287 184 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 183
    simpa using h
  have hprev := st287_p183
  have hstep := st287_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p185 : ((7730098535459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT287 (i+1))
      = (∑ i ∈ Finset.range 184, stT287 (i+1)) + stT287 185 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 184
    simpa using h
  have hprev := st287_p184
  have hstep := st287_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p186 : ((8031257214069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT287 (i+1))
      = (∑ i ∈ Finset.range 185, stT287 (i+1)) + stT287 186 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 185
    simpa using h
  have hprev := st287_p185
  have hstep := st287_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p187 : ((8707138285157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT287 (i+1))
      = (∑ i ∈ Finset.range 186, stT287 (i+1)) + stT287 187 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 186
    simpa using h
  have hprev := st287_p186
  have hstep := st287_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p188 : ((8456078364457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT287 (i+1))
      = (∑ i ∈ Finset.range 187, stT287 (i+1)) + stT287 188 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 187
    simpa using h
  have hprev := st287_p187
  have hstep := st287_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p189 : ((7761767198097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT287 (i+1))
      = (∑ i ∈ Finset.range 188, stT287 (i+1)) + stT287 189 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 188
    simpa using h
  have hprev := st287_p188
  have hstep := st287_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p190 : ((7938921182537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT287 (i+1))
      = (∑ i ∈ Finset.range 189, stT287 (i+1)) + stT287 190 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 189
    simpa using h
  have hprev := st287_p189
  have hstep := st287_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p191 : ((8650397025257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT287 (i+1))
      = (∑ i ∈ Finset.range 190, stT287 (i+1)) + stT287 191 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 190
    simpa using h
  have hprev := st287_p190
  have hstep := st287_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p192 : ((1714154060293/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT287 (i+1))
      = (∑ i ∈ Finset.range 191, stT287 (i+1)) + stT287 192 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 191
    simpa using h
  have hprev := st287_p191
  have hstep := st287_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p193 : ((7851218473937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT287 (i+1))
      = (∑ i ∈ Finset.range 192, stT287 (i+1)) + stT287 193 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 192
    simpa using h
  have hprev := st287_p192
  have hstep := st287_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p194 : ((7810237374217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT287 (i+1))
      = (∑ i ∈ Finset.range 193, stT287 (i+1)) + stT287 194 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 193
    simpa using h
  have hprev := st287_p193
  have hstep := st287_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p195 : ((8517998620521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT287 (i+1))
      = (∑ i ∈ Finset.range 194, stT287 (i+1)) + stT287 195 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 194
    simpa using h
  have hprev := st287_p194
  have hstep := st287_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p196 : ((8698094154711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT287 (i+1))
      = (∑ i ∈ Finset.range 195, stT287 (i+1)) + stT287 196 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 195
    simpa using h
  have hprev := st287_p195
  have hstep := st287_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p197 : ((8032540795003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT287 (i+1))
      = (∑ i ∈ Finset.range 196, stT287 (i+1)) + stT287 197 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 196
    simpa using h
  have hprev := st287_p196
  have hstep := st287_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p198 : ((7702507068343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT287 (i+1))
      = (∑ i ∈ Finset.range 197, stT287 (i+1)) + stT287 198 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 197
    simpa using h
  have hprev := st287_p197
  have hstep := st287_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p199 : ((2071091452149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT287 (i+1))
      = (∑ i ∈ Finset.range 198, stT287 (i+1)) + stT287 199 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 198
    simpa using h
  have hprev := st287_p198
  have hstep := st287_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p200 : ((4380543740709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT287 (i+1))
      = (∑ i ∈ Finset.range 199, stT287 (i+1)) + stT287 200 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 199
    simpa using h
  have hprev := st287_p199
  have hstep := st287_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p201 : ((259726680477/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT287 (i+1))
      = (∑ i ∈ Finset.range 200, stT287 (i+1)) + stT287 201 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 200
    simpa using h
  have hprev := st287_p200
  have hstep := st287_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p202 : ((385474797849/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT287 (i+1))
      = (∑ i ∈ Finset.range 201, stT287 (i+1)) + stT287 202 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 201
    simpa using h
  have hprev := st287_p201
  have hstep := st287_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p203 : ((498574922331/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT287 (i+1))
      = (∑ i ∈ Finset.range 202, stT287 (i+1)) + stT287 203 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 202
    simpa using h
  have hprev := st287_p202
  have hstep := st287_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p204 : ((2164669481469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT287 (i+1))
      = (∑ i ∈ Finset.range 203, stT287 (i+1)) + stT287 204 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 203
    simpa using h
  have hprev := st287_p203
  have hstep := st287_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p205 : ((4307111396363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT287 (i+1))
      = (∑ i ∈ Finset.range 204, stT287 (i+1)) + stT287 205 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 204
    simpa using h
  have hprev := st287_p204
  have hstep := st287_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p206 : ((3960838082033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT287 (i+1))
      = (∑ i ∈ Finset.range 205, stT287 (i+1)) + stT287 206 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 205
    simpa using h
  have hprev := st287_p205
  have hstep := st287_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p207 : ((7721807178577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT287 (i+1))
      = (∑ i ∈ Finset.range 206, stT287 (i+1)) + stT287 207 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 206
    simpa using h
  have hprev := st287_p206
  have hstep := st287_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p208 : ((16283209871/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT287 (i+1))
      = (∑ i ∈ Finset.range 207, stT287 (i+1)) + stT287 208 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 207
    simpa using h
  have hprev := st287_p207
  have hstep := st287_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p209 : ((548023998307/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT287 (i+1))
      = (∑ i ∈ Finset.range 208, stT287 (i+1)) + stT287 209 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 208
    simpa using h
  have hprev := st287_p208
  have hstep := st287_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p210 : ((2081413892257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT287 (i+1))
      = (∑ i ∈ Finset.range 209, stT287 (i+1)) + stT287 210 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 209
    simpa using h
  have hprev := st287_p209
  have hstep := st287_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p211 : ((154357079933/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT287 (i+1))
      = (∑ i ∈ Finset.range 210, stT287 (i+1)) + stT287 211 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 210
    simpa using h
  have hprev := st287_p210
  have hstep := st287_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p212 : ((3952212566777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT287 (i+1))
      = (∑ i ∈ Finset.range 211, stT287 (i+1)) + stT287 212 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 211
    simpa using h
  have hprev := st287_p211
  have hstep := st287_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p213 : ((858850792531/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT287 (i+1))
      = (∑ i ∈ Finset.range 212, stT287 (i+1)) + stT287 213 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 212
    simpa using h
  have hprev := st287_p212
  have hstep := st287_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p214 : ((870510565159/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT287 (i+1))
      = (∑ i ∈ Finset.range 213, stT287 (i+1)) + stT287 214 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 213
    simpa using h
  have hprev := st287_p213
  have hstep := st287_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p215 : ((50487681131/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT287 (i+1))
      = (∑ i ∈ Finset.range 214, stT287 (i+1)) + stT287 215 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 214
    simpa using h
  have hprev := st287_p214
  have hstep := st287_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p216 : ((958726995311/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT287 (i+1))
      = (∑ i ∈ Finset.range 215, stT287 (i+1)) + stT287 216 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 215
    simpa using h
  have hprev := st287_p215
  have hstep := st287_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p217 : ((506113769753/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT287 (i+1))
      = (∑ i ∈ Finset.range 216, stT287 (i+1)) + stT287 217 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 216
    simpa using h
  have hprev := st287_p216
  have hstep := st287_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p218 : ((8713082942173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT287 (i+1))
      = (∑ i ∈ Finset.range 217, stT287 (i+1)) + stT287 218 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 217
    simpa using h
  have hprev := st287_p217
  have hstep := st287_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p219 : ((8596180268173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT287 (i+1))
      = (∑ i ∈ Finset.range 218, stT287 (i+1)) + stT287 219 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 218
    simpa using h
  have hprev := st287_p218
  have hstep := st287_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p220 : ((7924611670773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT287 (i+1))
      = (∑ i ∈ Finset.range 219, stT287 (i+1)) + stT287 220 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 219
    simpa using h
  have hprev := st287_p219
  have hstep := st287_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p221 : ((7688395820093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT287 (i+1))
      = (∑ i ∈ Finset.range 220, stT287 (i+1)) + stT287 221 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 220
    simpa using h
  have hprev := st287_p220
  have hstep := st287_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p222 : ((8229131443861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT287 (i+1))
      = (∑ i ∈ Finset.range 221, stT287 (i+1)) + stT287 222 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 221
    simpa using h
  have hprev := st287_p221
  have hstep := st287_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p223 : ((2189921410281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT287 (i+1))
      = (∑ i ∈ Finset.range 222, stT287 (i+1)) + stT287 223 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 222
    simpa using h
  have hprev := st287_p222
  have hstep := st287_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p224 : ((4259185232703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT287 (i+1))
      = (∑ i ∈ Finset.range 223, stT287 (i+1)) + stT287 224 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 223
    simpa using h
  have hprev := st287_p223
  have hstep := st287_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p225 : ((7853613466361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT287 (i+1))
      = (∑ i ∈ Finset.range 224, stT287 (i+1)) + stT287 225 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 224
    simpa using h
  have hprev := st287_p224
  have hstep := st287_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p226 : ((1541539965873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT287 (i+1))
      = (∑ i ∈ Finset.range 225, stT287 (i+1)) + stT287 226 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 225
    simpa using h
  have hprev := st287_p225
  have hstep := st287_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p227 : ((1656411832929/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT287 (i+1))
      = (∑ i ∈ Finset.range 226, stT287 (i+1)) + stT287 227 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 226
    simpa using h
  have hprev := st287_p226
  have hstep := st287_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p228 : ((8772478396167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT287 (i+1))
      = (∑ i ∈ Finset.range 227, stT287 (i+1)) + stT287 228 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 227
    simpa using h
  have hprev := st287_p227
  have hstep := st287_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p229 : ((2125431743667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT287 (i+1))
      = (∑ i ∈ Finset.range 228, stT287 (i+1)) + stT287 229 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 228
    simpa using h
  have hprev := st287_p228
  have hstep := st287_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p230 : ((490355812039/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT287 (i+1))
      = (∑ i ∈ Finset.range 229, stT287 (i+1)) + stT287 230 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 229
    simpa using h
  have hprev := st287_p229
  have hstep := st287_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p231 : ((96244342231/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT287 (i+1))
      = (∑ i ∈ Finset.range 230, stT287 (i+1)) + stT287 231 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 230
    simpa using h
  have hprev := st287_p230
  have hstep := st287_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p232 : ((1032185339473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT287 (i+1))
      = (∑ i ∈ Finset.range 231, stT287 (i+1)) + stT287 232 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 231
    simpa using h
  have hprev := st287_p231
  have hstep := st287_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p233 : ((4383522500639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT287 (i+1))
      = (∑ i ∈ Finset.range 232, stT287 (i+1)) + stT287 233 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 232
    simpa using h
  have hprev := st287_p232
  have hstep := st287_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p234 : ((855033126001/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT287 (i+1))
      = (∑ i ∈ Finset.range 233, stT287 (i+1)) + stT287 234 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 233
    simpa using h
  have hprev := st287_p233
  have hstep := st287_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p235 : ((246811388279/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT287 (i+1))
      = (∑ i ∈ Finset.range 234, stT287 (i+1)) + stT287 235 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 234
    simpa using h
  have hprev := st287_p234
  have hstep := st287_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p236 : ((3833920523319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT287 (i+1))
      = (∑ i ∈ Finset.range 235, stT287 (i+1)) + stT287 236 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 235
    simpa using h
  have hprev := st287_p235
  have hstep := st287_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p237 : ((1631353417191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT287 (i+1))
      = (∑ i ∈ Finset.range 236, stT287 (i+1)) + stT287 237 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 236
    simpa using h
  have hprev := st287_p236
  have hstep := st287_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p238 : ((8728659739577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT287 (i+1))
      = (∑ i ∈ Finset.range 237, stT287 (i+1)) + stT287 238 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 237
    simpa using h
  have hprev := st287_p237
  have hstep := st287_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p239 : ((4324783908173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT287 (i+1))
      = (∑ i ∈ Finset.range 238, stT287 (i+1)) + stT287 239 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 238
    simpa using h
  have hprev := st287_p238
  have hstep := st287_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p240 : ((4012034317691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT287 (i+1))
      = (∑ i ∈ Finset.range 239, stT287 (i+1)) + stT287 240 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 239
    simpa using h
  have hprev := st287_p239
  have hstep := st287_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p241 : ((7645842190477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT287 (i+1))
      = (∑ i ∈ Finset.range 240, stT287 (i+1)) + stT287 241 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 240
    simpa using h
  have hprev := st287_p240
  have hstep := st287_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p242 : ((7987771846909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT287 (i+1))
      = (∑ i ∈ Finset.range 241, stT287 (i+1)) + stT287 242 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 241
    simpa using h
  have hprev := st287_p241
  have hstep := st287_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p243 : ((8619555687909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT287 (i+1))
      = (∑ i ∈ Finset.range 242, stT287 (i+1)) + stT287 243 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 242
    simpa using h
  have hprev := st287_p242
  have hstep := st287_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p244 : ((350329396269/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT287 (i+1))
      = (∑ i ∈ Finset.range 243, stT287 (i+1)) + stT287 244 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 243
    simpa using h
  have hprev := st287_p243
  have hstep := st287_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p245 : ((2059128633027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT287 (i+1))
      = (∑ i ∈ Finset.range 244, stT287 (i+1)) + stT287 245 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 244
    simpa using h
  have hprev := st287_p244
  have hstep := st287_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p246 : ((3847054325449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT287 (i+1))
      = (∑ i ∈ Finset.range 245, stT287 (i+1)) + stT287 246 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 245
    simpa using h
  have hprev := st287_p245
  have hstep := st287_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p247 : ((778731662149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT287 (i+1))
      = (∑ i ∈ Finset.range 246, stT287 (i+1)) + stT287 247 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 246
    simpa using h
  have hprev := st287_p246
  have hstep := st287_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p248 : ((840023894149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT287 (i+1))
      = (∑ i ∈ Finset.range 247, stT287 (i+1)) + stT287 248 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 247
    simpa using h
  have hprev := st287_p247
  have hstep := st287_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p249 : ((4399319203113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT287 (i+1))
      = (∑ i ∈ Finset.range 248, stT287 (i+1)) + stT287 249 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 248
    simpa using h
  have hprev := st287_p248
  have hstep := st287_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p250 : ((4255970204661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT287 (i+1))
      = (∑ i ∈ Finset.range 249, stT287 (i+1)) + stT287 250 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 249
    simpa using h
  have hprev := st287_p249
  have hstep := st287_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p251 : ((3940664316751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT287 (i+1))
      = (∑ i ∈ Finset.range 250, stT287 (i+1)) + stT287 251 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 250
    simpa using h
  have hprev := st287_p250
  have hstep := st287_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p252 : ((1911261015953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT287 (i+1))
      = (∑ i ∈ Finset.range 251, stT287 (i+1)) + stT287 252 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 251
    simpa using h
  have hprev := st287_p251
  have hstep := st287_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p253 : ((201863912203/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT287 (i+1))
      = (∑ i ∈ Finset.range 252, stT287 (i+1)) + stT287 253 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 252
    simpa using h
  have hprev := st287_p252
  have hstep := st287_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p254 : ((173426905049/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT287 (i+1))
      = (∑ i ∈ Finset.range 253, stT287 (i+1)) + stT287 254 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 253
    simpa using h
  have hprev := st287_p253
  have hstep := st287_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p255 : ((4376069084017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT287 (i+1))
      = (∑ i ∈ Finset.range 254, stT287 (i+1)) + stT287 255 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 254
    simpa using h
  have hprev := st287_p254
  have hstep := st287_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p256 : ((4114127414911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT287 (i+1))
      = (∑ i ∈ Finset.range 255, stT287 (i+1)) + stT287 256 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 255
    simpa using h
  have hprev := st287_p255
  have hstep := st287_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p257 : ((7693783208413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT287 (i+1))
      = (∑ i ∈ Finset.range 256, stT287 (i+1)) + stT287 257 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 256
    simpa using h
  have hprev := st287_p256
  have hstep := st287_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p258 : ((7746999417829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT287 (i+1))
      = (∑ i ∈ Finset.range 257, stT287 (i+1)) + stT287 258 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 257
    simpa using h
  have hprev := st287_p257
  have hstep := st287_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p259 : ((4162579519469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT287 (i+1))
      = (∑ i ∈ Finset.range 258, stT287 (i+1)) + stT287 259 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 258
    simpa using h
  have hprev := st287_p258
  have hstep := st287_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p260 : ((8786766826471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT287 (i+1))
      = (∑ i ∈ Finset.range 259, stT287 (i+1)) + stT287 260 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 259
    simpa using h
  have hprev := st287_p259
  have hstep := st287_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p261 : ((8626339532141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT287 (i+1))
      = (∑ i ∈ Finset.range 260, stT287 (i+1)) + stT287 261 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 260
    simpa using h
  have hprev := st287_p260
  have hstep := st287_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p262 : ((8022203570107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT287 (i+1))
      = (∑ i ∈ Finset.range 261, stT287 (i+1)) + stT287 262 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 261
    simpa using h
  have hprev := st287_p261
  have hstep := st287_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p263 : ((7630263116367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT287 (i+1))
      = (∑ i ∈ Finset.range 262, stT287 (i+1)) + stT287 263 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 262
    simpa using h
  have hprev := st287_p262
  have hstep := st287_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p264 : ((7870162100397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT287 (i+1))
      = (∑ i ∈ Finset.range 263, stT287 (i+1)) + stT287 264 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 263
    simpa using h
  have hprev := st287_p263
  have hstep := st287_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p265 : ((4241083197171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT287 (i+1))
      = (∑ i ∈ Finset.range 264, stT287 (i+1)) + stT287 265 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 264
    simpa using h
  have hprev := st287_p264
  have hstep := st287_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p266 : ((4407784654769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT287 (i+1))
      = (∑ i ∈ Finset.range 265, stT287 (i+1)) + stT287 266 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 265
    simpa using h
  have hprev := st287_p265
  have hstep := st287_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p267 : ((8521096988077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT287 (i+1))
      = (∑ i ∈ Finset.range 266, stT287 (i+1)) + stT287 267 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 266
    simpa using h
  have hprev := st287_p266
  have hstep := st287_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p268 : ((7910192790061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT287 (i+1))
      = (∑ i ∈ Finset.range 267, stT287 (i+1)) + stT287 268 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 267
    simpa using h
  have hprev := st287_p267
  have hstep := st287_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p269 : ((152378664713/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT287 (i+1))
      = (∑ i ∈ Finset.range 268, stT287 (i+1)) + stT287 269 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 268
    simpa using h
  have hprev := st287_p268
  have hstep := st287_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p270 : ((794575347583/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT287 (i+1))
      = (∑ i ∈ Finset.range 269, stT287 (i+1)) + stT287 270 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 269
    simpa using h
  have hprev := st287_p269
  have hstep := st287_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p271 : ((4276077162379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT287 (i+1))
      = (∑ i ∈ Finset.range 270, stT287 (i+1)) + stT287 271 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 270
    simpa using h
  have hprev := st287_p270
  have hstep := st287_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p272 : ((1102420535503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT287 (i+1))
      = (∑ i ∈ Finset.range 271, stT287 (i+1)) + stT287 272 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 271
    simpa using h
  have hprev := st287_p271
  have hstep := st287_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p273 : ((16958412351/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT287 (i+1))
      = (∑ i ∈ Finset.range 272, stT287 (i+1)) + stT287 273 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 272
    simpa using h
  have hprev := st287_p272
  have hstep := st287_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p274 : ((1575347090381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT287 (i+1))
      = (∑ i ∈ Finset.range 273, stT287 (i+1)) + stT287 274 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 273
    simpa using h
  have hprev := st287_p273
  have hstep := st287_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p275 : ((3807197861481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT287 (i+1))
      = (∑ i ∈ Finset.range 274, stT287 (i+1)) + stT287 275 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 274
    simpa using h
  have hprev := st287_p274
  have hstep := st287_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p276 : ((7950115001493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT287 (i+1))
      = (∑ i ∈ Finset.range 275, stT287 (i+1)) + stT287 276 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 275
    simpa using h
  have hprev := st287_p275
  have hstep := st287_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p277 : ((4274925527447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT287 (i+1))
      = (∑ i ∈ Finset.range 276, stT287 (i+1)) + stT287 277 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 276
    simpa using h
  have hprev := st287_p276
  have hstep := st287_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p278 : ((4412731782887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT287 (i+1))
      = (∑ i ∈ Finset.range 277, stT287 (i+1)) + stT287 278 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 277
    simpa using h
  have hprev := st287_p277
  have hstep := st287_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p279 : ((531937018489/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT287 (i+1))
      = (∑ i ∈ Finset.range 278, stT287 (i+1)) + stT287 279 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 278
    simpa using h
  have hprev := st287_p278
  have hstep := st287_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p280 : ((1978335359731/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT287 (i+1))
      = (∑ i ∈ Finset.range 279, stT287 (i+1)) + stT287 280 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 279
    simpa using h
  have hprev := st287_p279
  have hstep := st287_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p281 : ((3803628501437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT287 (i+1))
      = (∑ i ∈ Finset.range 280, stT287 (i+1)) + stT287 281 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 280
    simpa using h
  have hprev := st287_p280
  have hstep := st287_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p282 : ((1970661049447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT287 (i+1))
      = (∑ i ∈ Finset.range 281, stT287 (i+1)) + stT287 282 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 281
    simpa using h
  have hprev := st287_p281
  have hstep := st287_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p283 : ((4237697888591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT287 (i+1))
      = (∑ i ∈ Finset.range 282, stT287 (i+1)) + stT287 283 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 282
    simpa using h
  have hprev := st287_p282
  have hstep := st287_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p284 : ((2206523651923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT287 (i+1))
      = (∑ i ∈ Finset.range 283, stT287 (i+1)) + stT287 284 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 283
    simpa using h
  have hprev := st287_p283
  have hstep := st287_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p285 : ((4304167041807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT287 (i+1))
      = (∑ i ∈ Finset.range 284, stT287 (i+1)) + stT287 285 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 284
    simpa using h
  have hprev := st287_p284
  have hstep := st287_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p286 : ((8027511567547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT287 (i+1))
      = (∑ i ∈ Finset.range 285, stT287 (i+1)) + stT287 286 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 285
    simpa using h
  have hprev := st287_p285
  have hstep := st287_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p287 : ((7621552795713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT287 (i+1))
      = (∑ i ∈ Finset.range 286, stT287 (i+1)) + stT287 287 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 286
    simpa using h
  have hprev := st287_p286
  have hstep := st287_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p288 : ((7761569211793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT287 (i+1))
      = (∑ i ∈ Finset.range 287, stT287 (i+1)) + stT287 288 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 287
    simpa using h
  have hprev := st287_p287
  have hstep := st287_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p289 : ((4158427702369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT287 (i+1))
      = (∑ i ∈ Finset.range 288, stT287 (i+1)) + stT287 289 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 288
    simpa using h
  have hprev := st287_p288
  have hstep := st287_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p290 : ((4391173230199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT287 (i+1))
      = (∑ i ∈ Finset.range 289, stT287 (i+1)) + stT287 290 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 289
    simpa using h
  have hprev := st287_p289
  have hstep := st287_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p291 : ((8739798679807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT287 (i+1))
      = (∑ i ∈ Finset.range 290, stT287 (i+1)) + stT287 291 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 290
    simpa using h
  have hprev := st287_p290
  have hstep := st287_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p292 : ((65840453993/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT287 (i+1))
      = (∑ i ∈ Finset.range 291, stT287 (i+1)) + stT287 292 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 291
    simpa using h
  have hprev := st287_p291
  have hstep := st287_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p293 : ((7708484918423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT287 (i+1))
      = (∑ i ∈ Finset.range 292, stT287 (i+1)) + stT287 293 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 292
    simpa using h
  have hprev := st287_p292
  have hstep := st287_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p294 : ((305418577727/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT287 (i+1))
      = (∑ i ∈ Finset.range 293, stT287 (i+1)) + stT287 294 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 293
    simpa using h
  have hprev := st287_p293
  have hstep := st287_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p295 : ((8072473871933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT287 (i+1))
      = (∑ i ∈ Finset.range 294, stT287 (i+1)) + stT287 295 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 294
    simpa using h
  have hprev := st287_p294
  have hstep := st287_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p296 : ((8635649901083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT287 (i+1))
      = (∑ i ∈ Finset.range 295, stT287 (i+1)) + stT287 296 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 295
    simpa using h
  have hprev := st287_p295
  have hstep := st287_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p297 : ((8836351278897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT287 (i+1))
      = (∑ i ∈ Finset.range 296, stT287 (i+1)) + stT287 297 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 296
    simpa using h
  have hprev := st287_p296
  have hstep := st287_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p298 : ((8503772174697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT287 (i+1))
      = (∑ i ∈ Finset.range 297, stT287 (i+1)) + stT287 298 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 297
    simpa using h
  have hprev := st287_p297
  have hstep := st287_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p299 : ((7925400499827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT287 (i+1))
      = (∑ i ∈ Finset.range 298, stT287 (i+1)) + stT287 299 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 298
    simpa using h
  have hprev := st287_p298
  have hstep := st287_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p300 : ((7594387850997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT287 (i+1))
      = (∑ i ∈ Finset.range 299, stT287 (i+1)) + stT287 300 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 299
    simpa using h
  have hprev := st287_p299
  have hstep := st287_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p301 : ((7789065879057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT287 (i+1))
      = (∑ i ∈ Finset.range 300, stT287 (i+1)) + stT287 301 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 300
    simpa using h
  have hprev := st287_p300
  have hstep := st287_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p302 : ((8342940480477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT287 (i+1))
      = (∑ i ∈ Finset.range 301, stT287 (i+1)) + stT287 302 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 301
    simpa using h
  have hprev := st287_p301
  have hstep := st287_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p303 : ((8791556759529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT287 (i+1))
      = (∑ i ∈ Finset.range 302, stT287 (i+1)) + stT287 303 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 302
    simpa using h
  have hprev := st287_p302
  have hstep := st287_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p304 : ((8763197500689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT287 (i+1))
      = (∑ i ∈ Finset.range 303, stT287 (i+1)) + stT287 304 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 303
    simpa using h
  have hprev := st287_p303
  have hstep := st287_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p305 : ((4141922265021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT287 (i+1))
      = (∑ i ∈ Finset.range 304, stT287 (i+1)) + stT287 305 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 304
    simpa using h
  have hprev := st287_p304
  have hstep := st287_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p306 : ((1937220093033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT287 (i+1))
      = (∑ i ∈ Finset.range 305, stT287 (i+1)) + stT287 306 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 305
    simpa using h
  have hprev := st287_p305
  have hstep := st287_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p307 : ((7594454831807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT287 (i+1))
      = (∑ i ∈ Finset.range 306, stT287 (i+1)) + stT287 307 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 306
    simpa using h
  have hprev := st287_p306
  have hstep := st287_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p308 : ((7943499582551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT287 (i+1))
      = (∑ i ∈ Finset.range 307, stT287 (i+1)) + stT287 308 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 307
    simpa using h
  have hprev := st287_p307
  have hstep := st287_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p309 : ((8512220296151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT287 (i+1))
      = (∑ i ∈ Finset.range 308, stT287 (i+1)) + stT287 309 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 308
    simpa using h
  have hprev := st287_p308
  have hstep := st287_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p310 : ((4422133951771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT287 (i+1))
      = (∑ i ∈ Finset.range 309, stT287 (i+1)) + stT287 310 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 309
    simpa using h
  have hprev := st287_p309
  have hstep := st287_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p311 : ((4338374724643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT287 (i+1))
      = (∑ i ∈ Finset.range 310, stT287 (i+1)) + stT287 311 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 310
    simpa using h
  have hprev := st287_p310
  have hstep := st287_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p312 : ((814481430311/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT287 (i+1))
      = (∑ i ∈ Finset.range 311, stT287 (i+1)) + stT287 312 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 311
    simpa using h
  have hprev := st287_p311
  have hstep := st287_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p313 : ((1917124457221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT287 (i+1))
      = (∑ i ∈ Finset.range 312, stT287 (i+1)) + stT287 313 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 312
    simpa using h
  have hprev := st287_p312
  have hstep := st287_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p314 : ((7619631670081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT287 (i+1))
      = (∑ i ∈ Finset.range 313, stT287 (i+1)) + stT287 314 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 313
    simpa using h
  have hprev := st287_p313
  have hstep := st287_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p315 : ((8033817981169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT287 (i+1))
      = (∑ i ∈ Finset.range 314, stT287 (i+1)) + stT287 315 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 314
    simpa using h
  have hprev := st287_p314
  have hstep := st287_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p316 : ((4294339165709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT287 (i+1))
      = (∑ i ∈ Finset.range 315, stT287 (i+1)) + stT287 316 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 315
    simpa using h
  have hprev := st287_p315
  have hstep := st287_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p317 : ((1107185380561/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT287 (i+1))
      = (∑ i ∈ Finset.range 316, stT287 (i+1)) + stT287 317 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 316
    simpa using h
  have hprev := st287_p316
  have hstep := st287_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p318 : ((172731823903/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT287 (i+1))
      = (∑ i ∈ Finset.range 317, stT287 (i+1)) + stT287 318 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 317
    simpa using h
  have hprev := st287_p317
  have hstep := st287_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p319 : ((8096172953369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT287 (i+1))
      = (∑ i ∈ Finset.range 318, stT287 (i+1)) + stT287 319 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 318
    simpa using h
  have hprev := st287_p318
  have hstep := st287_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p320 : ((3822760419901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT287 (i+1))
      = (∑ i ∈ Finset.range 319, stT287 (i+1)) + stT287 320 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 319
    simpa using h
  have hprev := st287_p319
  have hstep := st287_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p321 : ((1905514235027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT287 (i+1))
      = (∑ i ∈ Finset.range 320, stT287 (i+1)) + stT287 321 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 320
    simpa using h
  have hprev := st287_p320
  have hstep := st287_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p322 : ((80409427507/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT287 (i+1))
      = (∑ i ∈ Finset.range 321, stT287 (i+1)) + stT287 322 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 321
    simpa using h
  have hprev := st287_p321
  have hstep := st287_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p323 : ((4294646321299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT287 (i+1))
      = (∑ i ∈ Finset.range 322, stT287 (i+1)) + stT287 323 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 322
    simpa using h
  have hprev := st287_p322
  have hstep := st287_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p324 : ((8862265147403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT287 (i+1))
      = (∑ i ∈ Finset.range 323, stT287 (i+1)) + stT287 324 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 323
    simpa using h
  have hprev := st287_p323
  have hstep := st287_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p325 : ((8661278115269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT287 (i+1))
      = (∑ i ∈ Finset.range 324, stT287 (i+1)) + stT287 325 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 324
    simpa using h
  have hprev := st287_p324
  have hstep := st287_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p326 : ((8135213504203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT287 (i+1))
      = (∑ i ∈ Finset.range 325, stT287 (i+1)) + stT287 326 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 325
    simpa using h
  have hprev := st287_p325
  have hstep := st287_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p327 : ((7666804220143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT287 (i+1))
      = (∑ i ∈ Finset.range 326, stT287 (i+1)) + stT287 327 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 326
    simpa using h
  have hprev := st287_p326
  have hstep := st287_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p328 : ((1518614802049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT287 (i+1))
      = (∑ i ∈ Finset.range 327, stT287 (i+1)) + stT287 328 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 327
    simpa using h
  have hprev := st287_p327
  have hstep := st287_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p329 : ((1592938949453/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT287 (i+1))
      = (∑ i ∈ Finset.range 328, stT287 (i+1)) + stT287 329 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 328
    simpa using h
  have hprev := st287_p328
  have hstep := st287_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p330 : ((8514679213403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT287 (i+1))
      = (∑ i ∈ Finset.range 329, stT287 (i+1)) + stT287 330 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 329
    simpa using h
  have hprev := st287_p329
  have hstep := st287_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p331 : ((8852652887013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT287 (i+1))
      = (∑ i ∈ Finset.range 330, stT287 (i+1)) + stT287 331 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 330
    simpa using h
  have hprev := st287_p330
  have hstep := st287_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p332 : ((8741740900211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT287 (i+1))
      = (∑ i ∈ Finset.range 331, stT287 (i+1)) + stT287 332 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 331
    simpa using h
  have hprev := st287_p331
  have hstep := st287_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p333 : ((8261894999119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT287 (i+1))
      = (∑ i ∈ Finset.range 332, stT287 (i+1)) + stT287 333 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 332
    simpa using h
  have hprev := st287_p332
  have hstep := st287_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p334 : ((7749033500431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT287 (i+1))
      = (∑ i ∈ Finset.range 333, stT287 (i+1)) + stT287 334 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 333
    simpa using h
  have hprev := st287_p333
  have hstep := st287_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p335 : ((3779159894407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT287 (i+1))
      = (∑ i ∈ Finset.range 334, stT287 (i+1)) + stT287 335 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 334
    simpa using h
  have hprev := st287_p334
  have hstep := st287_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p336 : ((6255454723/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT287 (i+1))
      = (∑ i ∈ Finset.range 335, stT287 (i+1)) + stT287 336 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 335
    simpa using h
  have hprev := st287_p335
  have hstep := st287_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p337 : ((4175498109619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT287 (i+1))
      = (∑ i ∈ Finset.range 336, stT287 (i+1)) + stT287 337 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 336
    simpa using h
  have hprev := st287_p336
  have hstep := st287_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p338 : ((878999180519/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT287 (i+1))
      = (∑ i ∈ Finset.range 337, stT287 (i+1)) + stT287 338 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 337
    simpa using h
  have hprev := st287_p337
  have hstep := st287_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p339 : ((441977706697/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT287 (i+1))
      = (∑ i ∈ Finset.range 338, stT287 (i+1)) + stT287 339 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 338
    simpa using h
  have hprev := st287_p338
  have hstep := st287_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p340 : ((169365866791/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT287 (i+1))
      = (∑ i ∈ Finset.range 339, stT287 (i+1)) + stT287 340 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 339
    simpa using h
  have hprev := st287_p339
  have hstep := st287_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p341 : ((3963445070433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT287 (i+1))
      = (∑ i ∈ Finset.range 340, stT287 (i+1)) + stT287 341 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 340
    simpa using h
  have hprev := st287_p340
  have hstep := st287_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p342 : ((7576652949827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT287 (i+1))
      = (∑ i ∈ Finset.range 341, stT287 (i+1)) + stT287 342 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 341
    simpa using h
  have hprev := st287_p341
  have hstep := st287_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p343 : ((478029979097/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT287 (i+1))
      = (∑ i ∈ Finset.range 342, stT287 (i+1)) + stT287 343 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 342
    simpa using h
  have hprev := st287_p342
  have hstep := st287_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p344 : ((252902480521/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT287 (i+1))
      = (∑ i ∈ Finset.range 343, stT287 (i+1)) + stT287 344 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 343
    simpa using h
  have hprev := st287_p343
  have hstep := st287_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p345 : ((8616863530351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT287 (i+1))
      = (∑ i ∈ Finset.range 344, stT287 (i+1)) + stT287 345 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 344
    simpa using h
  have hprev := st287_p344
  have hstep := st287_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p346 : ((8878686943411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT287 (i+1))
      = (∑ i ∈ Finset.range 345, stT287 (i+1)) + stT287 346 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 345
    simpa using h
  have hprev := st287_p345
  have hstep := st287_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p347 : ((4355011662023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT287 (i+1))
      = (∑ i ∈ Finset.range 346, stT287 (i+1)) + stT287 347 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 346
    simpa using h
  have hprev := st287_p346
  have hstep := st287_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p348 : ((4110845203321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT287 (i+1))
      = (∑ i ∈ Finset.range 347, stT287 (i+1)) + stT287 348 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 347
    simpa using h
  have hprev := st287_p347
  have hstep := st287_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p349 : ((3864108749669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT287 (i+1))
      = (∑ i ∈ Finset.range 348, stT287 (i+1)) + stT287 349 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 348
    simpa using h
  have hprev := st287_p348
  have hstep := st287_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p350 : ((754412991623/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT287 (i+1))
      = (∑ i ∈ Finset.range 349, stT287 (i+1)) + stT287 350 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 349
    simpa using h
  have hprev := st287_p349
  have hstep := st287_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p351 : ((778454769671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT287 (i+1))
      = (∑ i ∈ Finset.range 350, stT287 (i+1)) + stT287 351 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 350
    simpa using h
  have hprev := st287_p350
  have hstep := st287_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p352 : ((8295700452719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT287 (i+1))
      = (∑ i ∈ Finset.range 351, stT287 (i+1)) + stT287 352 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 351
    simpa using h
  have hprev := st287_p351
  have hstep := st287_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p353 : ((8755615818057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT287 (i+1))
      = (∑ i ∈ Finset.range 352, stT287 (i+1)) + stT287 353 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 352
    simpa using h
  have hprev := st287_p352
  have hstep := st287_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p354 : ((8877595817033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT287 (i+1))
      = (∑ i ∈ Finset.range 353, stT287 (i+1)) + stT287 354 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 353
    simpa using h
  have hprev := st287_p353
  have hstep := st287_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p355 : ((2146903831277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT287 (i+1))
      = (∑ i ∈ Finset.range 354, stT287 (i+1)) + stT287 355 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 354
    simpa using h
  have hprev := st287_p354
  have hstep := st287_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p356 : ((201666558701/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT287 (i+1))
      = (∑ i ∈ Finset.range 355, stT287 (i+1)) + stT287 356 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 355
    simpa using h
  have hprev := st287_p355
  have hstep := st287_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p357 : ((7635695253281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT287 (i+1))
      = (∑ i ∈ Finset.range 356, stT287 (i+1)) + stT287 357 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 356
    simpa using h
  have hprev := st287_p356
  have hstep := st287_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p358 : ((7557429284819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT287 (i+1))
      = (∑ i ∈ Finset.range 357, stT287 (i+1)) + stT287 358 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 357
    simpa using h
  have hprev := st287_p357
  have hstep := st287_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p359 : ((7877631748561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT287 (i+1))
      = (∑ i ∈ Finset.range 358, stT287 (i+1)) + stT287 359 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 358
    simpa using h
  have hprev := st287_p358
  have hstep := st287_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p360 : ((8400808176829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT287 (i+1))
      = (∑ i ∈ Finset.range 359, stT287 (i+1)) + stT287 360 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 359
    simpa using h
  have hprev := st287_p359
  have hstep := st287_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p361 : ((1101428379323/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT287 (i+1))
      = (∑ i ∈ Finset.range 360, stT287 (i+1)) + stT287 361 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 360
    simpa using h
  have hprev := st287_p360
  have hstep := st287_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p362 : ((2216115898519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT287 (i+1))
      = (∑ i ∈ Finset.range 361, stT287 (i+1)) + stT287 362 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 361
    simpa using h
  have hprev := st287_p361
  have hstep := st287_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p363 : ((2132524614503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT287 (i+1))
      = (∑ i ∈ Finset.range 362, stT287 (i+1)) + stT287 363 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 362
    simpa using h
  have hprev := st287_p362
  have hstep := st287_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p364 : ((500503644983/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT287 (i+1))
      = (∑ i ∈ Finset.range 363, stT287 (i+1)) + stT287 364 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 363
    simpa using h
  have hprev := st287_p363
  have hstep := st287_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p365 : ((475409128151/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT287 (i+1))
      = (∑ i ∈ Finset.range 364, stT287 (i+1)) + stT287 365 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 364
    simpa using h
  have hprev := st287_p364
  have hstep := st287_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p366 : ((7560085060951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT287 (i+1))
      = (∑ i ∈ Finset.range 365, stT287 (i+1)) + stT287 366 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 365
    simpa using h
  have hprev := st287_p365
  have hstep := st287_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p367 : ((7893981250681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT287 (i+1))
      = (∑ i ∈ Finset.range 366, stT287 (i+1)) + stT287 367 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 366
    simpa using h
  have hprev := st287_p366
  have hstep := st287_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p368 : ((8412831802489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT287 (i+1))
      = (∑ i ∈ Finset.range 367, stT287 (i+1)) + stT287 368 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 367
    simpa using h
  have hprev := st287_p367
  have hstep := st287_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p369 : ((8816528323093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT287 (i+1))
      = (∑ i ∈ Finset.range 368, stT287 (i+1)) + stT287 369 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 368
    simpa using h
  have hprev := st287_p368
  have hstep := st287_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p370 : ((8874007782593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT287 (i+1))
      = (∑ i ∈ Finset.range 369, stT287 (i+1)) + stT287 370 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 369
    simpa using h
  have hprev := st287_p369
  have hstep := st287_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p371 : ((4277058274409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT287 (i+1))
      = (∑ i ∈ Finset.range 370, stT287 (i+1)) + stT287 371 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 370
    simpa using h
  have hprev := st287_p370
  have hstep := st287_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p372 : ((4020136565939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT287 (i+1))
      = (∑ i ∈ Finset.range 371, stT287 (i+1)) + stT287 372 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 371
    simpa using h
  have hprev := st287_p371
  have hstep := st287_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p373 : ((476478964537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT287 (i+1))
      = (∑ i ∈ Finset.range 372, stT287 (i+1)) + stT287 373 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 372
    simpa using h
  have hprev := st287_p372
  have hstep := st287_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p374 : ((471120930999/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT287 (i+1))
      = (∑ i ∈ Finset.range 373, stT287 (i+1)) + stT287 374 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 373
    simpa using h
  have hprev := st287_p373
  have hstep := st287_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p375 : ((3914713788081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT287 (i+1))
      = (∑ i ∈ Finset.range 374, stT287 (i+1)) + stT287 375 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 374
    simpa using h
  have hprev := st287_p374
  have hstep := st287_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p376 : ((4167061005281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT287 (i+1))
      = (∑ i ∈ Finset.range 375, stT287 (i+1)) + stT287 376 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 375
    simpa using h
  have hprev := st287_p375
  have hstep := st287_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p377 : ((4385800272871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT287 (i+1))
      = (∑ i ∈ Finset.range 376, stT287 (i+1)) + stT287 377 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 376
    simpa using h
  have hprev := st287_p376
  have hstep := st287_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p378 : ((4450602730603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT287 (i+1))
      = (∑ i ∈ Finset.range 377, stT287 (i+1)) + stT287 378 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 377
    simpa using h
  have hprev := st287_p377
  have hstep := st287_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p379 : ((4326667452787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT287 (i+1))
      = (∑ i ∈ Finset.range 378, stT287 (i+1)) + stT287 379 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 378
    simpa using h
  have hprev := st287_p378
  have hstep := st287_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p380 : ((4082459076277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT287 (i+1))
      = (∑ i ∈ Finset.range 379, stT287 (i+1)) + stT287 380 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 379
    simpa using h
  have hprev := st287_p379
  have hstep := st287_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p381 : ((770204115887/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT287 (i+1))
      = (∑ i ∈ Finset.range 380, stT287 (i+1)) + stT287 381 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 380
    simpa using h
  have hprev := st287_p380
  have hstep := st287_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p382 : ((751443731001/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT287 (i+1))
      = (∑ i ∈ Finset.range 381, stT287 (i+1)) + stT287 382 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 381
    simpa using h
  have hprev := st287_p381
  have hstep := st287_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p383 : ((770153628217/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT287 (i+1))
      = (∑ i ∈ Finset.range 382, stT287 (i+1)) + stT287 383 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 382
    simpa using h
  have hprev := st287_p382
  have hstep := st287_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p384 : ((81615618657/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT287 (i+1))
      = (∑ i ∈ Finset.range 383, stT287 (i+1)) + stT287 384 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 383
    simpa using h
  have hprev := st287_p383
  have hstep := st287_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p385 : ((8648545373257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT287 (i+1))
      = (∑ i ∈ Finset.range 384, stT287 (i+1)) + stT287 385 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 384
    simpa using h
  have hprev := st287_p384
  have hstep := st287_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p386 : ((8904624882619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT287 (i+1))
      = (∑ i ∈ Finset.range 385, stT287 (i+1)) + stT287 386 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 385
    simpa using h
  have hprev := st287_p385
  have hstep := st287_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p387 : ((8796005141899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT287 (i+1))
      = (∑ i ∈ Finset.range 386, stT287 (i+1)) + stT287 387 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 386
    simpa using h
  have hprev := st287_p386
  have hstep := st287_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p388 : ((8381270005731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT287 (i+1))
      = (∑ i ∈ Finset.range 387, stT287 (i+1)) + stT287 388 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 387
    simpa using h
  have hprev := st287_p387
  have hstep := st287_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p389 : ((7878081070449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT287 (i+1))
      = (∑ i ∈ Finset.range 388, stT287 (i+1)) + stT287 389 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 388
    simpa using h
  have hprev := st287_p388
  have hstep := st287_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p390 : ((7547918209419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT287 (i+1))
      = (∑ i ∈ Finset.range 389, stT287 (i+1)) + stT287 390 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 389
    simpa using h
  have hprev := st287_p389
  have hstep := st287_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p391 : ((3780213609177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT287 (i+1))
      = (∑ i ∈ Finset.range 390, stT287 (i+1)) + stT287 391 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 390
    simpa using h
  have hprev := st287_p390
  have hstep := st287_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p392 : ((3953786259571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT287 (i+1))
      = (∑ i ∈ Finset.range 391, stT287 (i+1)) + stT287 392 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 391
    simpa using h
  have hprev := st287_p391
  have hstep := st287_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p393 : ((4205137152543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT287 (i+1))
      = (∑ i ∈ Finset.range 392, stT287 (i+1)) + stT287 393 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 392
    simpa using h
  have hprev := st287_p392
  have hstep := st287_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p394 : ((4405992977439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT287 (i+1))
      = (∑ i ∈ Finset.range 393, stT287 (i+1)) + stT287 394 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 393
    simpa using h
  have hprev := st287_p393
  have hstep := st287_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p395 : ((2227433043249/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT287 (i+1))
      = (∑ i ∈ Finset.range 394, stT287 (i+1)) + stT287 395 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 394
    simpa using h
  have hprev := st287_p394
  have hstep := st287_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p396 : ((33810985683/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT287 (i+1))
      = (∑ i ∈ Finset.range 395, stT287 (i+1)) + stT287 396 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 395
    simpa using h
  have hprev := st287_p395
  have hstep := st287_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p397 : ((4089334783581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT287 (i+1))
      = (∑ i ∈ Finset.range 396, stT287 (i+1)) + stT287 397 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 396
    simpa using h
  have hprev := st287_p396
  have hstep := st287_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p398 : ((7717938527637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT287 (i+1))
      = (∑ i ∈ Finset.range 397, stT287 (i+1)) + stT287 398 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 397
    simpa using h
  have hprev := st287_p397
  have hstep := st287_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p399 : ((7502173296907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT287 (i+1))
      = (∑ i ∈ Finset.range 398, stT287 (i+1)) + stT287 399 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 398
    simpa using h
  have hprev := st287_p398
  have hstep := st287_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p400 : ((7636891296907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT287 (i+1))
      = (∑ i ∈ Finset.range 399, stT287 (i+1)) + stT287 400 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 399
    simpa using h
  have hprev := st287_p399
  have hstep := st287_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p401 : ((1610840268639/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT287 (i+1))
      = (∑ i ∈ Finset.range 400, stT287 (i+1)) + stT287 401 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 400
    simpa using h
  have hprev := st287_p400
  have hstep := st287_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p402 : ((8548465559687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT287 (i+1))
      = (∑ i ∈ Finset.range 401, stT287 (i+1)) + stT287 402 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 401
    simpa using h
  have hprev := st287_p401
  have hstep := st287_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p403 : ((8878455090437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT287 (i+1))
      = (∑ i ∈ Finset.range 402, stT287 (i+1)) + stT287 403 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 402
    simpa using h
  have hprev := st287_p402
  have hstep := st287_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p404 : ((8884845709147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT287 (i+1))
      = (∑ i ∈ Finset.range 403, stT287 (i+1)) + stT287 404 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 403
    simpa using h
  have hprev := st287_p403
  have hstep := st287_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p405 : ((8565984896867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT287 (i+1))
      = (∑ i ∈ Finset.range 404, stT287 (i+1)) + stT287 405 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 404
    simpa using h
  have hprev := st287_p404
  have hstep := st287_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p406 : ((8076502519399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT287 (i+1))
      = (∑ i ∈ Finset.range 405, stT287 (i+1)) + stT287 406 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 405
    simpa using h
  have hprev := st287_p405
  have hstep := st287_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p407 : ((7651192492939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT287 (i+1))
      = (∑ i ∈ Finset.range 406, stT287 (i+1)) + stT287 407 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 406
    simpa using h
  have hprev := st287_p406
  have hstep := st287_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p408 : ((7492157396549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT287 (i+1))
      = (∑ i ∈ Finset.range 407, stT287 (i+1)) + stT287 408 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 407
    simpa using h
  have hprev := st287_p407
  have hstep := st287_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p409 : ((7673515897249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT287 (i+1))
      = (∑ i ∈ Finset.range 408, stT287 (i+1)) + stT287 409 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 408
    simpa using h
  have hprev := st287_p408
  have hstep := st287_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p410 : ((1621643393101/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT287 (i+1))
      = (∑ i ∈ Finset.range 409, stT287 (i+1)) + stT287 410 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 409
    simpa using h
  have hprev := st287_p409
  have hstep := st287_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p411 : ((8591115523349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT287 (i+1))
      = (∑ i ∈ Finset.range 410, stT287 (i+1)) + stT287 411 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 410
    simpa using h
  have hprev := st287_p410
  have hstep := st287_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p412 : ((8896420882141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT287 (i+1))
      = (∑ i ∈ Finset.range 411, stT287 (i+1)) + stT287 412 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 411
    simpa using h
  have hprev := st287_p411
  have hstep := st287_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p413 : ((8882962330273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT287 (i+1))
      = (∑ i ∈ Finset.range 412, stT287 (i+1)) + stT287 413 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 412
    simpa using h
  have hprev := st287_p412
  have hstep := st287_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p414 : ((8558349650961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT287 (i+1))
      = (∑ i ∈ Finset.range 413, stT287 (i+1)) + stT287 414 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 413
    simpa using h
  have hprev := st287_p413
  have hstep := st287_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p415 : ((8073460344447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT287 (i+1))
      = (∑ i ∈ Finset.range 414, stT287 (i+1)) + stT287 415 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 414
    simpa using h
  have hprev := st287_p414
  have hstep := st287_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p416 : ((306051968049/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT287 (i+1))
      = (∑ i ∈ Finset.range 415, stT287 (i+1)) + stT287 416 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 415
    simpa using h
  have hprev := st287_p415
  have hstep := st287_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p417 : ((7484238002181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT287 (i+1))
      = (∑ i ∈ Finset.range 416, stT287 (i+1)) + stT287 417 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 416
    simpa using h
  have hprev := st287_p416
  have hstep := st287_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p418 : ((1911755458169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT287 (i+1))
      = (∑ i ∈ Finset.range 417, stT287 (i+1)) + stT287 418 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 417
    simpa using h
  have hprev := st287_p417
  have hstep := st287_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p419 : ((4032286104781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT287 (i+1))
      = (∑ i ∈ Finset.range 418, stT287 (i+1)) + stT287 419 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 418
    simpa using h
  have hprev := st287_p418
  have hstep := st287_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p420 : ((4273899426781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT287 (i+1))
      = (∑ i ∈ Finset.range 419, stT287 (i+1)) + stT287 420 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 419
    simpa using h
  have hprev := st287_p419
  have hstep := st287_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p421 : ((4439935663641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT287 (i+1))
      = (∑ i ∈ Finset.range 420, stT287 (i+1)) + stT287 421 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 420
    simpa using h
  have hprev := st287_p420
  have hstep := st287_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p422 : ((4456654048089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT287 (i+1))
      = (∑ i ∈ Finset.range 421, stT287 (i+1)) + stT287 422 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 421
    simpa using h
  have hprev := st287_p421
  have hstep := st287_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p423 : ((1726910130391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT287 (i+1))
      = (∑ i ∈ Finset.range 422, stT287 (i+1)) + stT287 423 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 422
    simpa using h
  have hprev := st287_p422
  have hstep := st287_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p424 : ((2042033200349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT287 (i+1))
      = (∑ i ∈ Finset.range 423, stT287 (i+1)) + stT287 424 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 423
    simpa using h
  have hprev := st287_p423
  have hstep := st287_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p425 : ((1930017099873/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT287 (i+1))
      = (∑ i ∈ Finset.range 424, stT287 (i+1)) + stT287 425 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 424
    simpa using h
  have hprev := st287_p424
  have hstep := st287_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p426 : ((3743257347447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT287 (i+1))
      = (∑ i ∈ Finset.range 425, stT287 (i+1)) + stT287 426 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 425
    simpa using h
  have hprev := st287_p425
  have hstep := st287_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p427 : ((7568363734983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT287 (i+1))
      = (∑ i ∈ Finset.range 426, stT287 (i+1)) + stT287 427 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 426
    simpa using h
  have hprev := st287_p426
  have hstep := st287_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p428 : ((1585738952179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT287 (i+1))
      = (∑ i ∈ Finset.range 427, stT287 (i+1)) + stT287 428 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 427
    simpa using h
  have hprev := st287_p427
  have hstep := st287_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p429 : ((8410592537787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT287 (i+1))
      = (∑ i ∈ Finset.range 428, stT287 (i+1)) + stT287 429 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 428
    simpa using h
  have hprev := st287_p428
  have hstep := st287_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p430 : ((1761239856049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT287 (i+1))
      = (∑ i ∈ Finset.range 429, stT287 (i+1)) + stT287 430 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 429
    simpa using h
  have hprev := st287_p429
  have hstep := st287_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p431 : ((1118306304709/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT287 (i+1))
      = (∑ i ∈ Finset.range 430, stT287 (i+1)) + stT287 431 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 430
    simpa using h
  have hprev := st287_p430
  have hstep := st287_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p432 : ((2193153219527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT287 (i+1))
      = (∑ i ∈ Finset.range 431, stT287 (i+1)) + stT287 432 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 431
    simpa using h
  have hprev := st287_p431
  have hstep := st287_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p433 : ((4179895136359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT287 (i+1))
      = (∑ i ∈ Finset.range 432, stT287 (i+1)) + stT287 433 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 432
    simpa using h
  have hprev := st287_p432
  have hstep := st287_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p434 : ((3941718637407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT287 (i+1))
      = (∑ i ∈ Finset.range 433, stT287 (i+1)) + stT287 434 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 433
    simpa using h
  have hprev := st287_p433
  have hstep := st287_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p435 : ((3772103692499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT287 (i+1))
      = (∑ i ∈ Finset.range 434, stT287 (i+1)) + stT287 435 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 434
    simpa using h
  have hprev := st287_p434
  have hstep := st287_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p436 : ((935447647853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT287 (i+1))
      = (∑ i ∈ Finset.range 435, stT287 (i+1)) + stT287 436 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 435
    simpa using h
  have hprev := st287_p435
  have hstep := st287_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p437 : ((1931408461297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT287 (i+1))
      = (∑ i ∈ Finset.range 436, stT287 (i+1)) + stT287 437 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 436
    simpa using h
  have hprev := st287_p436
  have hstep := st287_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p438 : ((4084292971773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT287 (i+1))
      = (∑ i ∈ Finset.range 437, stT287 (i+1)) + stT287 438 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 437
    simpa using h
  have hprev := st287_p437
  have hstep := st287_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p439 : ((8628470456337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT287 (i+1))
      = (∑ i ∈ Finset.range 438, stT287 (i+1)) + stT287 439 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 438
    simpa using h
  have hprev := st287_p438
  have hstep := st287_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p440 : ((4457972246689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT287 (i+1))
      = (∑ i ∈ Finset.range 439, stT287 (i+1)) + stT287 440 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 439
    simpa using h
  have hprev := st287_p439
  have hstep := st287_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p441 : ((1782786707757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT287 (i+1))
      = (∑ i ∈ Finset.range 440, stT287 (i+1)) + stT287 441 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 440
    simpa using h
  have hprev := st287_p440
  have hstep := st287_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p442 : ((8624448402021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT287 (i+1))
      = (∑ i ∈ Finset.range 441, stT287 (i+1)) + stT287 442 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 441
    simpa using h
  have hprev := st287_p441
  have hstep := st287_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p443 : ((2041562467899/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT287 (i+1))
      = (∑ i ∈ Finset.range 442, stT287 (i+1)) + stT287 443 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 442
    simpa using h
  have hprev := st287_p442
  have hstep := st287_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p444 : ((3862659735927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT287 (i+1))
      = (∑ i ∈ Finset.range 443, stT287 (i+1)) + stT287 444 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 443
    simpa using h
  have hprev := st287_p443
  have hstep := st287_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p445 : ((3739549989727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT287 (i+1))
      = (∑ i ∈ Finset.range 444, stT287 (i+1)) + stT287 445 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 444
    simpa using h
  have hprev := st287_p444
  have hstep := st287_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p446 : ((7525475369161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT287 (i+1))
      = (∑ i ∈ Finset.range 445, stT287 (i+1)) + stT287 446 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 445
    simpa using h
  have hprev := st287_p445
  have hstep := st287_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p447 : ((1568938129979/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT287 (i+1))
      = (∑ i ∈ Finset.range 446, stT287 (i+1)) + stT287 447 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 446
    simpa using h
  have hprev := st287_p446
  have hstep := st287_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p448 : ((20771829247/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT287 (i+1))
      = (∑ i ∈ Finset.range 447, stT287 (i+1)) + stT287 448 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 447
    simpa using h
  have hprev := st287_p447
  have hstep := st287_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p449 : ((68229214329/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT287 (i+1))
      = (∑ i ∈ Finset.range 448, stT287 (i+1)) + stT287 449 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 448
    simpa using h
  have hprev := st287_p448
  have hstep := st287_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p450 : ((1118918469547/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT287 (i+1))
      = (∑ i ∈ Finset.range 449, stT287 (i+1)) + stT287 450 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 449
    simpa using h
  have hprev := st287_p449
  have hstep := st287_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p451 : ((4439024896687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT287 (i+1))
      = (∑ i ∈ Finset.range 450, stT287 (i+1)) + stT287 451 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 450
    simpa using h
  have hprev := st287_p450
  have hstep := st287_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p452 : ((1708654164397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT287 (i+1))
      = (∑ i ∈ Finset.range 451, stT287 (i+1)) + stT287 452 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 451
    simpa using h
  have hprev := st287_p451
  have hstep := st287_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p453 : ((8078291736653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT287 (i+1))
      = (∑ i ∈ Finset.range 452, stT287 (i+1)) + stT287 453 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 452
    simpa using h
  have hprev := st287_p452
  have hstep := st287_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p454 : ((7663737378129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT287 (i+1))
      = (∑ i ∈ Finset.range 453, stT287 (i+1)) + stT287 454 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 453
    simpa using h
  have hprev := st287_p453
  have hstep := st287_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p455 : ((1491857291773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT287 (i+1))
      = (∑ i ∈ Finset.range 454, stT287 (i+1)) + stT287 455 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 454
    simpa using h
  have hprev := st287_p454
  have hstep := st287_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p456 : ((7542580620321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT287 (i+1))
      = (∑ i ∈ Finset.range 455, stT287 (i+1)) + stT287 456 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 455
    simpa using h
  have hprev := st287_p455
  have hstep := st287_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p457 : ((7880564300381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT287 (i+1))
      = (∑ i ∈ Finset.range 456, stT287 (i+1)) + stT287 457 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 456
    simpa using h
  have hprev := st287_p456
  have hstep := st287_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p458 : ((2085869938777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT287 (i+1))
      = (∑ i ∈ Finset.range 457, stT287 (i+1)) + stT287 458 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 457
    simpa using h
  have hprev := st287_p457
  have hstep := st287_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p459 : ((2188812223117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT287 (i+1))
      = (∑ i ∈ Finset.range 458, stT287 (i+1)) + stT287 459 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 458
    simpa using h
  have hprev := st287_p458
  have hstep := st287_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p460 : ((448028754161/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT287 (i+1))
      = (∑ i ∈ Finset.range 459, stT287 (i+1)) + stT287 460 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 459
    simpa using h
  have hprev := st287_p459
  have hstep := st287_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p461 : ((555190893097/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT287 (i+1))
      = (∑ i ∈ Finset.range 460, stT287 (i+1)) + stT287 461 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 460
    simpa using h
  have hprev := st287_p460
  have hstep := st287_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p462 : ((26727658943/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT287 (i+1))
      = (∑ i ∈ Finset.range 461, stT287 (i+1)) + stT287 462 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 461
    simpa using h
  have hprev := st287_p461
  have hstep := st287_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p463 : ((404704672989/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT287 (i+1))
      = (∑ i ∈ Finset.range 462, stT287 (i+1)) + stT287 463 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 462
    simpa using h
  have hprev := st287_p462
  have hstep := st287_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p464 : ((7677642758201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT287 (i+1))
      = (∑ i ∈ Finset.range 463, stT287 (i+1)) + stT287 464 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 463
    simpa using h
  have hprev := st287_p463
  have hstep := st287_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p465 : ((7457320359301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT287 (i+1))
      = (∑ i ∈ Finset.range 464, stT287 (i+1)) + stT287 465 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 464
    simpa using h
  have hprev := st287_p464
  have hstep := st287_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p466 : ((7513451271271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT287 (i+1))
      = (∑ i ∈ Finset.range 465, stT287 (i+1)) + stT287 466 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 465
    simpa using h
  have hprev := st287_p465
  have hstep := st287_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p467 : ((7824326855167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT287 (i+1))
      = (∑ i ∈ Finset.range 466, stT287 (i+1)) + stT287 467 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 466
    simpa using h
  have hprev := st287_p466
  have hstep := st287_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p468 : ((8275376999917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT287 (i+1))
      = (∑ i ∈ Finset.range 467, stT287 (i+1)) + stT287 468 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 467
    simpa using h
  have hprev := st287_p467
  have hstep := st287_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p469 : ((1087747150901/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT287 (i+1))
      = (∑ i ∈ Finset.range 468, stT287 (i+1)) + stT287 469 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 468
    simpa using h
  have hprev := st287_p468
  have hstep := st287_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p470 : ((8949691733953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT287 (i+1))
      = (∑ i ∈ Finset.range 469, stT287 (i+1)) + stT287 470 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 469
    simpa using h
  have hprev := st287_p469
  have hstep := st287_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p471 : ((8929859013361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT287 (i+1))
      = (∑ i ∈ Finset.range 470, stT287 (i+1)) + stT287 471 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 470
    simpa using h
  have hprev := st287_p470
  have hstep := st287_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p472 : ((1730129478397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT287 (i+1))
      = (∑ i ∈ Finset.range 471, stT287 (i+1)) + stT287 472 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 471
    simpa using h
  have hprev := st287_p471
  have hstep := st287_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p473 : ((4106480720341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT287 (i+1))
      = (∑ i ∈ Finset.range 472, stT287 (i+1)) + stT287 473 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 472
    simpa using h
  have hprev := st287_p472
  have hstep := st287_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p474 : ((3886681019649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT287 (i+1))
      = (∑ i ∈ Finset.range 473, stT287 (i+1)) + stT287 474 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 473
    simpa using h
  have hprev := st287_p473
  have hstep := st287_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p475 : ((149756718657/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT287 (i+1))
      = (∑ i ∈ Finset.range 474, stT287 (i+1)) + stT287 475 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 474
    simpa using h
  have hprev := st287_p474
  have hstep := st287_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p476 : ((149133160983/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT287 (i+1))
      = (∑ i ∈ Finset.range 475, stT287 (i+1)) + stT287 476 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 475
    simpa using h
  have hprev := st287_p475
  have hstep := st287_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p477 : ((3844892831081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT287 (i+1))
      = (∑ i ∈ Finset.range 476, stT287 (i+1)) + stT287 477 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 476
    simpa using h
  have hprev := st287_p476
  have hstep := st287_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p478 : ((126632087731/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT287 (i+1))
      = (∑ i ∈ Finset.range 477, stT287 (i+1)) + stT287 478 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 477
    simpa using h
  have hprev := st287_p477
  have hstep := st287_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p479 : ((8555161134137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT287 (i+1))
      = (∑ i ∈ Finset.range 478, stT287 (i+1)) + stT287 479 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 478
    simpa using h
  have hprev := st287_p478
  have hstep := st287_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p480 : ((2221258160573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT287 (i+1))
      = (∑ i ∈ Finset.range 479, stT287 (i+1)) + stT287 480 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 479
    simpa using h
  have hprev := st287_p479
  have hstep := st287_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p481 : ((2245074775213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT287 (i+1))
      = (∑ i ∈ Finset.range 480, stT287 (i+1)) + stT287 481 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 480
    simpa using h
  have hprev := st287_p480
  have hstep := st287_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p482 : ((2202246946653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT287 (i+1))
      = (∑ i ∈ Finset.range 481, stT287 (i+1)) + stT287 482 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 481
    simpa using h
  have hprev := st287_p481
  have hstep := st287_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p483 : ((2107744901121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT287 (i+1))
      = (∑ i ∈ Finset.range 482, stT287 (i+1)) + stT287 483 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 482
    simpa using h
  have hprev := st287_p482
  have hstep := st287_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p484 : ((3988195211307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT287 (i+1))
      = (∑ i ∈ Finset.range 483, stT287 (i+1)) + stT287 484 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 483
    simpa using h
  have hprev := st287_p483
  have hstep := st287_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p485 : ((7600412396229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT287 (i+1))
      = (∑ i ∈ Finset.range 484, stT287 (i+1)) + stT287 485 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 484
    simpa using h
  have hprev := st287_p484
  have hstep := st287_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p486 : ((7430345842249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT287 (i+1))
      = (∑ i ∈ Finset.range 485, stT287 (i+1)) + stT287 486 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 485
    simpa using h
  have hprev := st287_p485
  have hstep := st287_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p487 : ((7522868579989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT287 (i+1))
      = (∑ i ∈ Finset.range 486, stT287 (i+1)) + stT287 487 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 486
    simpa using h
  have hprev := st287_p486
  have hstep := st287_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p488 : ((7845799558951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT287 (i+1))
      = (∑ i ∈ Finset.range 487, stT287 (i+1)) + stT287 488 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 487
    simpa using h
  have hprev := st287_p487
  have hstep := st287_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p489 : ((8289928954751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT287 (i+1))
      = (∑ i ∈ Finset.range 488, stT287 (i+1)) + stT287 489 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 488
    simpa using h
  have hprev := st287_p488
  have hstep := st287_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p490 : ((2176605545337/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT287 (i+1))
      = (∑ i ∈ Finset.range 489, stT287 (i+1)) + stT287 490 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 489
    simpa using h
  have hprev := st287_p489
  have hstep := st287_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p491 : ((2239196274093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT287 (i+1))
      = (∑ i ∈ Finset.range 490, stT287 (i+1)) + stT287 491 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 490
    simpa using h
  have hprev := st287_p490
  have hstep := st287_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p492 : ((559916679843/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT287 (i+1))
      = (∑ i ∈ Finset.range 491, stT287 (i+1)) + stT287 492 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 491
    simpa using h
  have hprev := st287_p491
  have hstep := st287_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p493 : ((4356194013441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT287 (i+1))
      = (∑ i ∈ Finset.range 492, stT287 (i+1)) + stT287 493 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 492
    simpa using h
  have hprev := st287_p492
  have hstep := st287_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p494 : ((4149924123087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT287 (i+1))
      = (∑ i ∈ Finset.range 493, stT287 (i+1)) + stT287 494 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 493
    simpa using h
  have hprev := st287_p493
  have hstep := st287_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p495 : ((785678525199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT287 (i+1))
      = (∑ i ∈ Finset.range 494, stT287 (i+1)) + stT287 495 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 494
    simpa using h
  have hprev := st287_p494
  have hstep := st287_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p496 : ((3763921491879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT287 (i+1))
      = (∑ i ∈ Finset.range 495, stT287 (i+1)) + stT287 496 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 495
    simpa using h
  have hprev := st287_p495
  have hstep := st287_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p497 : ((3709732510907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT287 (i+1))
      = (∑ i ∈ Finset.range 496, stT287 (i+1)) + stT287 497 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 496
    simpa using h
  have hprev := st287_p496
  have hstep := st287_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p498 : ((1891468888501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT287 (i+1))
      = (∑ i ∈ Finset.range 497, stT287 (i+1)) + stT287 498 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 497
    simpa using h
  have hprev := st287_p497
  have hstep := st287_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p499 : ((158377895027/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT287 (i+1))
      = (∑ i ∈ Finset.range 498, stT287 (i+1)) + stT287 499 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 498
    simpa using h
  have hprev := st287_p498
  have hstep := st287_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_p500 : ((418217510213/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT287 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT287 (i+1))
      = (∑ i ∈ Finset.range 499, stT287 (i+1)) + stT287 500 := by
    have h := Finset.sum_range_succ (fun i => stT287 (i+1)) 499
    simpa using h
  have hprev := st287_p499
  have hstep := st287_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st287_s500 :
    |Real.sin (((287 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))
      - ((-43721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -43777/2000000) (δ := 7231/500000000) (ψ := -744563/1000000) 287 284
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 287`** (evaluated boundary). -/
theorem station_287_sign : hardyG ((((287:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 287 500 (by norm_num) (by norm_num)
    ((-744563/1000000 : ℚ) : ℝ)
  have hchain := st287_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT287 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((287 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-744563/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st287_c500
  have hsinb := abs_le.mp st287_s500
  have hbdy_lo : ((10987584694047/1647385000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((287 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ))) / 2
          - ((((287:ℕ)):ℝ))
            * Real.sin (((287 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-744563/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((287:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((287:ℝ) * Real.log (500:ℝ) - ((-744563/1000000 : ℚ) : ℝ))) / 2
        - ((287:ℝ)) * Real.sin ((287:ℝ) * Real.log (500:ℝ) - ((-744563/1000000 : ℚ) : ℝ))
        ≥ ((24569019/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((287:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((24569019/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((24569019/1000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((24569019/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((287:ℕ)):ℝ))+1) * (((((287:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((201436589557/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((418217510213/500000000000 : ℚ) : ℝ) + ((10987584694047/1647385000000000 : ℚ) : ℝ)
      - ((201436589557/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-744563/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((287:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-744563/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((287:ℕ)):ℝ)))).re
      - Real.sin ((-744563/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((287:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((287:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((287:ℕ)):ℝ))
      = (((((287:ℕ)):ℝ)) * (Real.log ((((287:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((287:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_287
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
  have hθwin : |(((-744563/1000000 : ℚ) : ℝ) + ((65:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((287:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((287:ℕ)):ℝ)))
    (φ := ((-744563/1000000 : ℚ) : ℝ) + ((65:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-744563/1000000 : ℚ) : ℝ) + ((65:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-744563/1000000 : ℚ)) : ℝ) - Real.pi) + ((65:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-744563/1000000 : ℚ)) : ℝ) - Real.pi) 65).1,
    (cos_sin_shift ((((-744563/1000000 : ℚ)) : ℝ) - Real.pi) 65).2]
  exact cos_sin_flip ((-744563/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_287_sign
end AxiomAudit
