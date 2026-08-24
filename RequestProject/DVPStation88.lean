import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 88` (rung-91; thin window, evaluated boundary, N = 200)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT88 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((88 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-16027/31250 : ℚ) : ℝ))

theorem st88_c1 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((871343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1282159/10000000) (δ := 41/100000000) (ψ := -16027/31250) 88 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t1 : ((871293/1000000 : ℚ) : ℝ) ≤ stT88 1 := by
  have hc : ((871293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((871293/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((871293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c2 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((246201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305093/10000000) (δ := 709/100000000) (ψ := -16027/31250) 88 10
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t2 : ((1740550213117/10000000000000 : ℚ) : ℝ) ≤ stT88 2 := by
  have hc : ((246151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1740550213117/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((246151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c3 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-490169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3678707/5000000) (δ := 381/50000000) (ψ := -16027/31250) 88 15
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t3 : ((-1415068264791/2500000000000 : ℚ) : ℝ) ≤ stT88 3 := by
  have hc : ((-245097/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1415068264791/2500000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-245097/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c4 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-499941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7815617/10000000) (δ := 21/4000000) (ψ := -16027/31250) 88 19
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t4 : ((-1249915249983/2500000000000 : ℚ) : ℝ) ≤ stT88 4 := by
  have hc : ((-249983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1249915249983/2500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-249983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c5 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-143341/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1184931/2000000) (δ := 159/20000000) (ψ := -16027/31250) 88 23
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t5 : ((-80135645967/250000000000 : ℚ) : ℝ) ≤ stT88 5 := by
  have hc : ((-143351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80135645967/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-143351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c6 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((223197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2770161/10000000) (δ := 589/100000000) (ψ := -16027/31250) 88 25
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t6 : ((113886959113/625000000000 : ℚ) : ℝ) ≤ stT88 6 := by
  have hc : ((55793/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113886959113/625000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((55793/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c7 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-127709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658423/1250000) (δ := 59/12500000) (ψ := -16027/31250) 88 27
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t7 : ((-193096771547/1000000000000 : ℚ) : ℝ) ≤ stT88 7 := by
  have hc : ((-255443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193096771547/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-255443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c8 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((68957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 807091/2500000) (δ := 531/100000000) (ψ := -16027/31250) 88 29
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t8 : ((487511109837/5000000000000 : ℚ) : ℝ) ≤ stT88 8 := by
  have hc : ((137889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487511109837/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((137889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c9 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((613653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -455059/2000000) (δ := 327/50000000) (ψ := -16027/31250) 88 31
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t9 : ((2045343128799/10000000000000 : ℚ) : ℝ) ≤ stT88 9 := by
  have hc : ((613603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2045343128799/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((613603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c10 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-60763/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1039211/2000000) (δ := 49/6250000) (ψ := -16027/31250) 88 32
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t10 : ((-384338524703/2500000000000 : ℚ) : ℝ) ≤ stT88 10 := by
  have hc : ((-243077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384338524703/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-243077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c11 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-50541/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328227/625000) (δ := 303/50000000) (ψ := -16027/31250) 88 34
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t11 : ((-38100488061/250000000000 : ℚ) : ℝ) ≤ stT88 11 := by
  have hc : ((-25273/50000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38100488061/250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-25273/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c12 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((9341/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454273/2500000) (δ := 233/50000000) (ψ := -16027/31250) 88 35
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t12 : ((215706694973/1000000000000 : ℚ) : ℝ) ≤ stT88 12 := by
  have hc : ((74723/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215706694973/1000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((74723/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c13 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((999431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4217/500000) (δ := 467/100000000) (ψ := -16027/31250) 88 36
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t13 : ((5543566407/20000000000 : ℚ) : ℝ) ≤ stT88 13 := by
  have hc : ((999381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5543566407/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((999381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c14 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((963221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680131/10000000) (δ := 129/20000000) (ψ := -16027/31250) 88 37
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t14 : ((643545593163/2500000000000 : ℚ) : ℝ) ≤ stT88 14 := by
  have hc : ((963171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((643545593163/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((963171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c15 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((499093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 753/50000) (δ := 437/50000000) (ψ := -16027/31250) 88 38
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t15 : ((80536724199/312500000000 : ℚ) : ℝ) ≤ stT88 15 := by
  have hc : ((124767/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80536724199/312500000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((124767/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c16 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((6847/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1358889/10000000) (δ := 703/100000000) (ψ := -16027/31250) 88 39
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t16 : ((34233/160000 : ℚ) : ℝ) ≤ stT88 16 := by
  have hc : ((34233/40000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34233/160000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((34233/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c17 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((3947/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932359/2500000) (δ := 533/100000000) (ψ := -16027/31250) 88 40
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t17 : ((4783408371/250000000000 : ℚ) : ℝ) ≤ stT88 17 := by
  have hc : ((7889/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4783408371/250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((7889/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c18 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-92239/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1715637/2500000) (δ := 481/100000000) (ψ := -16027/31250) 88 41
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t18 : ((-54355307403/250000000000 : ℚ) : ℝ) ≤ stT88 18 := by
  have hc : ((-23061/25000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54355307403/250000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-23061/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c19 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-427839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5032241/10000000) (δ := 681/100000000) (ψ := -16027/31250) 88 41
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t19 : ((-490822486231/5000000000000 : ℚ) : ℝ) ≤ stT88 19 := by
  have hc : ((-427889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490822486231/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-427889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c20 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((194099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304401/5000000) (δ := 153/25000000) (ψ := -16027/31250) 88 42
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t20 : ((433996007963/2000000000000 : ℚ) : ℝ) ≤ stT88 20 := by
  have hc : ((194089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433996007963/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((194089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c21 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-174437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174613/400000) (δ := 581/100000000) (ψ := -16027/31250) 88 43
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t21 : ((-380761867173/10000000000000 : ℚ) : ℝ) ≤ stT88 21 := by
  have hc : ((-174487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-380761867173/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-174487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c22 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-350513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5869079/10000000) (δ := 231/50000000) (ψ := -16027/31250) 88 43
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t22 : ((-46709363769/312500000000 : ℚ) : ℝ) ≤ stT88 22 := by
  have hc : ((-175269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46709363769/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-175269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c23 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((999717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59497/10000000) (δ := 77/10000000) (ψ := -16027/31250) 88 44
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t23 : ((260556205881/1250000000000 : ℚ) : ℝ) ≤ stT88 23 := by
  have hc : ((999667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260556205881/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((999667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c24 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-418271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1280869/2000000) (δ := 639/100000000) (ψ := -16027/31250) 88 45
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t24 : ((-53365210227/312500000000 : ℚ) : ℝ) ≤ stT88 24 := by
  have hc : ((-52287/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53365210227/312500000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-52287/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c25 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((257153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1288247/5000000) (δ := 679/100000000) (ψ := -16027/31250) 88 45
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t25 : ((32141/312500 : ℚ) : ℝ) ≤ stT88 25 := by
  have hc : ((32141/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32141/312500 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((32141/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c26 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-14271/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35179/78125) (δ := 137/25000000) (ψ := -16027/31250) 88 46
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t26 : ((-111975486133/2500000000000 : ℚ) : ℝ) ≤ stT88 26 := by
  have hc : ((-114193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111975486133/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-114193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c27 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((5079/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94999/250000) (δ := 23/4000000) (ψ := -16027/31250) 88 46
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t27 : ((9764913/1000000000 : ℚ) : ℝ) ≤ stT88 27 := by
  have hc : ((2537/50000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9764913/1000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((2537/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c28 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((7947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1953561/5000000) (δ := 409/50000000) (ψ := -16027/31250) 88 47
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t28 : ((7461962167/5000000000000 : ℚ) : ℝ) ≤ stT88 28 := by
  have hc : ((7897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7461962167/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((7897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c29 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((45593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3812969/10000000) (δ := 309/50000000) (ψ := -16027/31250) 88 47
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t29 : ((84571210479/10000000000000 : ℚ) : ℝ) ≤ stT88 29 := by
  have hc : ((45543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84571210479/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((45543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c30 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-25307/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4436653/10000000) (δ := 179/25000000) (ψ := -16027/31250) 88 48
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t30 : ((-92430927363/2500000000000 : ℚ) : ℝ) ≤ stT88 30 := by
  have hc : ((-101253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92430927363/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-101253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c31 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((221953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694277/2500000) (δ := 847/100000000) (ψ := -16027/31250) 88 48
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t31 : ((49824306273/625000000000 : ℚ) : ℝ) ≤ stT88 31 := by
  have hc : ((27741/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49824306273/625000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((27741/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c32 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-45167/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2973071/5000000) (δ := 219/25000000) (ψ := -16027/31250) 88 49
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t32 : ((-638802050887/5000000000000 : ℚ) : ℝ) ≤ stT88 32 := by
  have hc : ((-361361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638802050887/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-361361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c33 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((946221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 823623/10000000) (δ := 527/100000000) (ψ := -16027/31250) 88 49
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t33 : ((205883971087/1250000000000 : ℚ) : ℝ) ≤ stT88 33 := by
  have hc : ((946171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205883971087/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((946171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c34 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-982921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295651/400000) (δ := 169/25000000) (ψ := -16027/31250) 88 49
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t34 : ((-842890751703/5000000000000 : ℚ) : ℝ) ≤ stT88 34 := by
  have hc : ((-982971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-842890751703/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-982971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c35 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((713881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193943/1000000) (δ := 537/100000000) (ψ := -16027/31250) 88 50
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t35 : ((301648562487/2500000000000 : ℚ) : ℝ) ≤ stT88 35 := by
  have hc : ((713831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301648562487/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((713831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c36 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-66041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4258163/10000000) (δ := 273/50000000) (ψ := -16027/31250) 88 50
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t36 : ((-55055011011/2500000000000 : ℚ) : ℝ) ≤ stT88 36 := by
  have hc : ((-33033/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55055011011/2500000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-33033/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c37 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-281501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2711013/5000000) (δ := 31/4000000) (ψ := -16027/31250) 88 51
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t37 : ((-23141296437/250000000000 : ℚ) : ℝ) ≤ stT88 37 := by
  have hc : ((-140763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23141296437/250000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-140763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c38 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((984201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 111247/2500000) (δ := 127/25000000) (ψ := -16027/31250) 88 51
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t38 : ((798251765157/5000000000000 : ℚ) : ℝ) ≤ stT88 38 := by
  have hc : ((984151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((798251765157/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((984151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c39 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-778983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1231919/2000000) (δ := 99/20000000) (ψ := -16027/31250) 88 51
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t39 : ((-623725760153/5000000000000 : ℚ) : ℝ) ≤ stT88 39 := by
  have hc : ((-779033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-623725760153/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-779033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c40 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-20583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3978451/10000000) (δ := 111/25000000) (ψ := -16027/31250) 88 52
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t40 : ((-32623640987/10000000000000 : ℚ) : ℝ) ≤ stT88 40 := by
  have hc : ((-20633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32623640987/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-20633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c41 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((835601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363481/2500000) (δ := 559/100000000) (ψ := -16027/31250) 88 52
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t41 : ((1304910912087/10000000000000 : ℚ) : ℝ) ≤ stT88 41 := by
  have hc : ((835551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1304910912087/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((835551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c42 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-904991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3377693/5000000) (δ := 181/25000000) (ψ := -16027/31250) 88 52
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t42 : ((-698254517197/5000000000000 : ℚ) : ℝ) ≤ stT88 42 := by
  have hc : ((-905041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-698254517197/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-905041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c43 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((15103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -943967/2500000) (δ := 753/100000000) (ψ := -16027/31250) 88 53
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t43 : ((9205114457/1000000000000 : ℚ) : ℝ) ≤ stT88 43 := by
  have hc : ((30181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9205114457/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((30181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c44 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((54463/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640913/5000000) (δ := 593/100000000) (ψ := -16027/31250) 88 53
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t44 : ((164202622631/1250000000000 : ℚ) : ℝ) ≤ stT88 44 := by
  have hc : ((435679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164202622631/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((435679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c45 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-397663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3112927/5000000) (δ := 77/10000000) (ψ := -16027/31250) 88 53
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t45 : ((-9263098029/78125000000 : ℚ) : ℝ) ≤ stT88 45 := by
  have hc : ((-49711/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9263098029/78125000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-49711/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c46 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-283943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18587/40000) (δ := 41/5000000) (ψ := -16027/31250) 88 54
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t46 : ((-20936247953/500000000000 : ℚ) : ℝ) ≤ stT88 46 := by
  have hc : ((-283993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20936247953/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-283993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c47 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((999427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16923/2000000) (δ := 903/100000000) (ψ := -16027/31250) 88 54
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t47 : ((1457740261673/10000000000000 : ℚ) : ℝ) ≤ stT88 47 := by
  have hc : ((999377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1457740261673/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((999377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c48 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-310529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 943273/2000000) (δ := 823/100000000) (ψ := -16027/31250) 88 54
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t48 : ((-28017642169/625000000000 : ℚ) : ℝ) ≤ stT88 48 := by
  have hc : ((-310579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28017642169/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-310579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c49 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-847547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1291071/2000000) (δ := 831/100000000) (ψ := -16027/31250) 88 55
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t49 : ((-302713335371/2500000000000 : ℚ) : ℝ) ≤ stT88 49 := by
  have hc : ((-847597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302713335371/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-847597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c50 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((693613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2010759/10000000) (δ := 213/25000000) (ψ := -16027/31250) 88 55
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t50 : ((980845810919/10000000000000 : ℚ) : ℝ) ≤ stT88 50 := by
  have hc : ((693563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((980845810919/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((693563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c51 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((295569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2345819/10000000) (δ := 153/25000000) (ψ := -16027/31250) 88 55
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t51 : ((1293263601/15625000000 : ℚ) : ℝ) ≤ stT88 51 := by
  have hc : ((36943/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1293263601/15625000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((36943/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c52 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-880219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3308899/5000000) (δ := 183/25000000) (ψ := -16027/31250) 88 55
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t52 : ((-1220713916019/10000000000000 : ℚ) : ℝ) ≤ stT88 52 := by
  have hc : ((-880269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1220713916019/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-880269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c53 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-37929/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4899563/10000000) (δ := 801/100000000) (ψ := -16027/31250) 88 56
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t53 : ((-13026592501/250000000000 : ℚ) : ℝ) ≤ stT88 53 := by
  have hc : ((-18967/50000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13026592501/250000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-18967/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c54 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((475411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -787293/10000000) (δ := 481/100000000) (ψ := -16027/31250) 88 56
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t54 : ((323459052111/2500000000000 : ℚ) : ℝ) ≤ stT88 54 := by
  have hc : ((237693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323459052111/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((237693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c55 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((53537/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3249517/10000000) (δ := 361/50000000) (ψ := -16027/31250) 88 56
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t55 : ((72175753273/2000000000000 : ℚ) : ℝ) ≤ stT88 55 := by
  have hc : ((53527/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72175753273/2000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((53527/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c56 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-967371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1803397/2500000) (δ := 381/50000000) (ψ := -16027/31250) 88 56
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t56 : ((-1292771454247/10000000000000 : ℚ) : ℝ) ≤ stT88 56 := by
  have hc : ((-967421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1292771454247/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-967421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c57 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-8317/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1150117/2500000) (δ := 143/25000000) (ψ := -16027/31250) 88 57
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t57 : ((-176291368701/5000000000000 : ℚ) : ℝ) ≤ stT88 57 := by
  have hc : ((-133097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176291368701/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-133097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c58 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((952421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193571/2500000) (δ := 791/100000000) (ψ := -16027/31250) 88 57
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t58 : ((156315509343/1250000000000 : ℚ) : ℝ) ≤ stT88 58 := by
  have hc : ((952371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156315509343/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((952371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c59 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((367389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2986491/10000000) (δ := 511/100000000) (ψ := -16027/31250) 88 57
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t59 : ((478234603371/10000000000000 : ℚ) : ℝ) ≤ stT88 59 := by
  have hc : ((367339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((478234603371/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((367339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c60 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-446243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6684057/10000000) (δ := 133/25000000) (ψ := -16027/31250) 88 57
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t60 : ((-28806487833/250000000000 : ℚ) : ℝ) ≤ stT88 60 := by
  have hc : ((-111567/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28806487833/250000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-111567/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c61 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-275761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269373/500000) (δ := 543/100000000) (ψ := -16027/31250) 88 58
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t61 : ((-176553922517/2500000000000 : ℚ) : ℝ) ≤ stT88 61 := by
  have hc : ((-137893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176553922517/2500000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-137893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c62 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((187281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362029/2000000) (δ := 743/100000000) (ψ := -16027/31250) 88 58
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t62 : ((475662364537/5000000000000 : ℚ) : ℝ) ≤ stT88 62 := by
  have hc : ((374537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475662364537/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((374537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c63 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((775069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170993/1000000) (δ := 33/5000000) (ψ := -16027/31250) 88 58
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t63 : ((976431712739/10000000000000 : ℚ) : ℝ) ≤ stT88 63 := by
  have hc : ((775019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((976431712739/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((775019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c64 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-19143/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 646821/1250000) (δ := 703/100000000) (ψ := -16027/31250) 88 58
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t64 : ((-4786253829/80000000000 : ℚ) : ℝ) ≤ stT88 64 := by
  have hc : ((-3829/8000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4786253829/80000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-3829/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c65 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-119687/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3561237/5000000) (δ := 297/50000000) (ψ := -16027/31250) 88 59
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t65 : ((-148461283251/1250000000000 : ℚ) : ℝ) ≤ stT88 65 := by
  have hc : ((-478773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148461283251/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-478773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c66 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((32649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -376363/1000000) (δ := 529/100000000) (ψ := -16027/31250) 88 59
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t66 : ((1254916823/156250000000 : ℚ) : ℝ) ≤ stT88 66 := by
  have hc : ((2039/31250 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1254916823/156250000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((2039/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c67 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((491731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -455297/10000000) (δ := 729/100000000) (ψ := -16027/31250) 88 59
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t67 : ((150178567491/1250000000000 : ℚ) : ℝ) ≤ stT88 67 := by
  have hc : ((245853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150178567491/1250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((245853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c68 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((217117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1402011/5000000) (δ := 849/100000000) (ψ := -16027/31250) 88 59
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t68 : ((32907836547/625000000000 : ℚ) : ℝ) ≤ stT88 68 := by
  have hc : ((54273/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32907836547/625000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((54273/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c69 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-741637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3007879/5000000) (δ := 849/100000000) (ψ := -16027/31250) 88 59
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t69 : ((-892886570133/10000000000000 : ℚ) : ℝ) ≤ stT88 69 := by
  have hc : ((-741687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-892886570133/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-741687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c70 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-431171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6526683/10000000) (δ := 259/50000000) (ψ := -16027/31250) 88 60
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t70 : ((-128844490971/1250000000000 : ℚ) : ℝ) ≤ stT88 70 := by
  have hc : ((-107799/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128844490971/1250000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-107799/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c71 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((103433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212879/625000) (δ := 129/20000000) (ψ := -16027/31250) 88 60
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t71 : ((7670165603/312500000000 : ℚ) : ℝ) ≤ stT88 71 := by
  have hc : ((6463/31250 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7670165603/312500000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((6463/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c72 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((247837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32909/1000000) (δ := 359/50000000) (ψ := -16027/31250) 88 60
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t72 : ((584127798639/5000000000000 : ℚ) : ℝ) ≤ stT88 72 := by
  have hc : ((495649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584127798639/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((495649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c73 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((14669/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16909/62500) (δ := 279/50000000) (ψ := -16027/31250) 88 60
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t73 : ((274670883069/5000000000000 : ℚ) : ℝ) ≤ stT88 73 := by
  have hc : ((234679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274670883069/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((234679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c74 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-65083/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1424671/2500000) (δ := 161/20000000) (ψ := -16027/31250) 88 60
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t74 : ((-1182239109/15625000000 : ℚ) : ℝ) ≤ stT88 74 := by
  have hc : ((-2034/3125 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1182239109/15625000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-2034/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c75 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-237379/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1411243/2000000) (δ := 197/25000000) (ψ := -16027/31250) 88 61
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t75 : ((-548232404883/5000000000000 : ℚ) : ℝ) ≤ stT88 75 := by
  have hc : ((-474783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548232404883/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-474783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c76 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-86003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -828453/2000000) (δ := 137/25000000) (ψ := -16027/31250) 88 61
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t76 : ((-98709589187/10000000000000 : ℚ) : ℝ) ≤ stT88 76 := by
  have hc : ((-86053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98709589187/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-86053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c77 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((874417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1266407/10000000) (δ := 177/25000000) (ψ := -16027/31250) 88 61
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t77 : ((199286601007/2000000000000 : ℚ) : ℝ) ≤ stT88 77 := by
  have hc : ((874367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199286601007/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((874367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c78 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((808653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 786171/5000000) (δ := 167/25000000) (ψ := -16027/31250) 88 61
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t78 : ((915562579031/10000000000000 : ℚ) : ℝ) ≤ stT88 78 := by
  have hc : ((808603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((915562579031/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((808603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c79 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-89109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273433/625000) (δ := 91/20000000) (ψ := -16027/31250) 88 61
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t79 : ((-1566931153/78125000000 : ℚ) : ℝ) ≤ stT88 79 := by
  have hc : ((-44567/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1566931153/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-44567/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c80 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-959749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357113/500000) (δ := 147/25000000) (ψ := -16027/31250) 88 61
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t80 : ((-536543957583/5000000000000 : ℚ) : ℝ) ≤ stT88 80 := by
  have hc : ((-959799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536543957583/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-959799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c81 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-690589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5832749/10000000) (δ := 233/50000000) (ψ := -16027/31250) 88 62
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t81 : ((-95922160071/1250000000000 : ℚ) : ℝ) ≤ stT88 81 := by
  have hc : ((-690639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95922160071/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-690639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c82 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((312159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3133329/10000000) (δ := 497/100000000) (ψ := -16027/31250) 88 62
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t82 : ((68933330067/2000000000000 : ℚ) : ℝ) ≤ stT88 82 := by
  have hc : ((312109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68933330067/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((312109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c83 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((982631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -466629/10000000) (δ := 817/100000000) (ψ := -16027/31250) 88 62
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t83 : ((539261087001/5000000000000 : ℚ) : ℝ) ≤ stT88 83 := by
  have hc : ((982581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539261087001/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((982581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c84 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((161731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2168133/10000000) (δ := 897/100000000) (ψ := -16027/31250) 88 62
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t84 : ((352898552893/5000000000000 : ℚ) : ℝ) ≤ stT88 84 := by
  have hc : ((323437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352898552893/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((323437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c85 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-41437/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4771713/10000000) (δ := 233/50000000) (ψ := -16027/31250) 88 62
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t85 : ((-179806181769/5000000000000 : ℚ) : ℝ) ≤ stT88 85 := by
  have hc : ((-165773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179806181769/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-165773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c86 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-489667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3672421/5000000) (δ := 413/50000000) (ψ := -16027/31250) 88 62
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t86 : ((-16501518593/156250000000 : ℚ) : ℝ) ≤ stT88 86 := by
  have hc : ((-122423/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16501518593/156250000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-122423/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c87 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-21463/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290987/500000) (δ := 363/50000000) (ψ := -16027/31250) 88 63
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t87 : ((-368198983929/5000000000000 : ℚ) : ℝ) ≤ stT88 87 := by
  have hc : ((-343433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368198983929/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-343433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c88 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((30759/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305427/10000000) (δ := 383/50000000) (ψ := -16027/31250) 88 63
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t88 : ((131130095033/5000000000000 : ℚ) : ℝ) ≤ stT88 88 := by
  have hc : ((123011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131130095033/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((123011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c89 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((3787/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32781/400000) (δ := 597/100000000) (ψ := -16027/31250) 88 63
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t89 : ((10034991599/100000000000 : ℚ) : ℝ) ≤ stT88 89 := by
  have hc : ((9467/10000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10034991599/100000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((9467/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c90 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((39639/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1638601/10000000) (δ := 597/100000000) (ψ := -16027/31250) 88 63
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t90 : ((20890258779/250000000000 : ℚ) : ℝ) ≤ stT88 90 := by
  have hc : ((79273/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20890258779/250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((79273/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c91 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-56999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813913/2000000) (δ := 917/100000000) (ψ := -16027/31250) 88 63
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t91 : ((-11960722193/2000000000000 : ℚ) : ℝ) ≤ stT88 91 := by
  have hc : ((-57049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11960722193/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-57049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c92 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-851473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6473961/10000000) (δ := 677/100000000) (ψ := -16027/31250) 88 63
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t92 : ((-887774888679/10000000000000 : ℚ) : ℝ) ≤ stT88 92 := by
  have hc : ((-851523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-887774888679/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-851523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c93 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-921313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6855601/10000000) (δ := 807/100000000) (ψ := -16027/31250) 88 64
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t93 : ((-119426150697/1250000000000 : ℚ) : ℝ) ≤ stT88 93 := by
  have hc : ((-921363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119426150697/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-921363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c94 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-22823/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2251319/5000000) (δ := 687/100000000) (ψ := -16027/31250) 88 64
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t94 : ((-2943162677/125000000000 : ℚ) : ℝ) ≤ stT88 94 := by
  have hc : ((-5707/25000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2943162677/125000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-5707/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c95 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((644957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2174573/10000000) (δ := 807/100000000) (ψ := -16027/31250) 88 64
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t95 : ((330830197023/5000000000000 : ℚ) : ℝ) ≤ stT88 95 := by
  have hc : ((644907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330830197023/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((644907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c96 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((998667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16139/1250000) (δ := 767/100000000) (ψ := -16027/31250) 88 64
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t96 : ((50960424127/500000000000 : ℚ) : ℝ) ≤ stT88 96 := by
  have hc : ((998617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50960424127/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((998617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c97 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((570591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1204463/5000000) (δ := 687/100000000) (ψ := -16027/31250) 88 64
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t97 : ((289648261093/5000000000000 : ℚ) : ℝ) ≤ stT88 97 := by
  have hc : ((570541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289648261093/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((570541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c98 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-291071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1166339/2500000) (δ := 687/100000000) (ψ := -16027/31250) 88 64
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t98 : ((-294076751513/10000000000000 : ℚ) : ℝ) ≤ stT88 98 := by
  have hc : ((-291121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294076751513/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-291121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c99 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-185581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6898877/10000000) (δ := 119/25000000) (ψ := -16027/31250) 88 64
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t99 : ((-93263003729/1000000000000 : ℚ) : ℝ) ≤ stT88 99 := by
  have hc : ((-185591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93263003729/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-185591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c100 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-175287/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1649503/2500000) (δ := 369/50000000) (ψ := -16027/31250) 88 65
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t100 : ((-175297/2000000 : ℚ) : ℝ) ≤ stT88 100 := by
  have hc : ((-175297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175297/2000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-175297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c101 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-191587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4408939/10000000) (δ := 149/20000000) (ψ := -16027/31250) 88 65
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t101 : ((-95343048603/5000000000000 : ℚ) : ℝ) ≤ stT88 101 := by
  have hc : ((-191637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95343048603/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-191637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c102 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((62429/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1120717/5000000) (δ := 157/20000000) (ψ := -16027/31250) 88 65
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t102 : ((7726117041/125000000000 : ℚ) : ℝ) ≤ stT88 102 := by
  have hc : ((7803/12500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7726117041/125000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((7803/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c103 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((999277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23769/2500000) (δ := 369/50000000) (ψ := -16027/31250) 88 65
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t103 : ((984567340683/10000000000000 : ℚ) : ℝ) ≤ stT88 103 := by
  have hc : ((999227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((984567340683/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((999227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c104 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((68789/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 406109/2000000) (δ := 429/50000000) (ψ := -16027/31250) 88 65
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t104 : ((210775671/3125000000 : ℚ) : ℝ) ≤ stT88 104 := by
  have hc : ((4299/6250 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210775671/3125000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((4299/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c105 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-20859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258489/625000) (δ := 93/20000000) (ψ := -16027/31250) 88 65
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t105 : ((-40737035443/5000000000000 : ℚ) : ℝ) ≤ stT88 105 := by
  have hc : ((-41743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40737035443/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-41743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c106 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-99273/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1555287/2500000) (δ := 409/50000000) (ψ := -16027/31250) 88 65
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t106 : ((-192857091231/2500000000000 : ℚ) : ℝ) ≤ stT88 106 := by
  have hc : ((-397117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192857091231/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-397117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c107 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-197009/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7421073/10000000) (δ := 307/50000000) (ψ := -16027/31250) 88 66
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t107 : ((-190465557003/2000000000000 : ℚ) : ℝ) ≤ stT88 107 := by
  have hc : ((-197019/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190465557003/2000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-197019/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c108 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-273603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2687273/5000000) (δ := 327/50000000) (ψ := -16027/31250) 88 66
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t108 : ((-65824704157/1250000000000 : ℚ) : ℝ) ≤ stT88 108 := by
  have hc : ((-68407/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65824704157/1250000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-68407/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c109 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((229967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1673441/5000000) (δ := 709/100000000) (ψ := -16027/31250) 88 66
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t109 : ((110110240221/5000000000000 : ℚ) : ℝ) ≤ stT88 109 := by
  have hc : ((229917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110110240221/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((229917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c110 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((43011/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167217/1250000) (δ := 549/100000000) (ψ := -16027/31250) 88 66
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t110 : ((41006970427/500000000000 : ℚ) : ℝ) ≤ stT88 110 := by
  have hc : ((86017/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41006970427/500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((86017/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c111 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((966057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 163307/2500000) (δ := 447/50000000) (ψ := -16027/31250) 88 66
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t111 : ((916892306099/10000000000000 : ℚ) : ℝ) ≤ stT88 111 := by
  have hc : ((966007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((916892306099/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((966007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c112 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((497107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82073/312500) (δ := 629/100000000) (ψ := -16027/31250) 88 66
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t112 : ((469674626927/10000000000000 : ℚ) : ℝ) ≤ stT88 112 := by
  have hc : ((497057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469674626927/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((497057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c113 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-258979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286369/625000) (δ := 367/50000000) (ψ := -16027/31250) 88 66
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t113 : ((-243674019909/10000000000000 : ℚ) : ℝ) ≤ stT88 113 := by
  have hc : ((-259029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243674019909/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-259029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c114 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-172207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3260121/5000000) (δ := 247/50000000) (ψ := -16027/31250) 88 66
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t114 : ((-80648015581/1000000000000 : ℚ) : ℝ) ≤ stT88 114 := by
  have hc : ((-172217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80648015581/1000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-172217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c115 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-486249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7266311/10000000) (δ := 643/100000000) (ψ := -16027/31250) 88 67
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t115 : ((-45345293637/500000000000 : ℚ) : ℝ) ≤ stT88 115 := by
  have hc : ((-243137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45345293637/500000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-243137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c116 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-542843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5361537/10000000) (δ := 1/125000) (ψ := -16027/31250) 88 67
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t116 : ((-504063663961/10000000000000 : ℚ) : ℝ) ≤ stT88 116 := by
  have hc : ((-542893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504063663961/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-542893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c117 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((36111/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1736557/5000000) (δ := 603/100000000) (ψ := -16027/31250) 88 67
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t117 : ((66750749/4000000000 : ℚ) : ℝ) ≤ stT88 117 := by
  have hc : ((36101/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66750749/4000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((36101/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c118 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((400957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -800381/5000000) (δ := 683/100000000) (ψ := -16027/31250) 88 67
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t118 : ((46135946871/625000000000 : ℚ) : ℝ) ≤ stT88 118 := by
  have hc : ((100233/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46135946871/625000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((100233/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c119 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((99477/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255789/10000000) (δ := 1/125000) (ψ := -16027/31250) 88 67
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t119 : ((2849555733/31250000000 : ℚ) : ℝ) ≤ stT88 119 := by
  have hc : ((6217/6250 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2849555733/31250000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((6217/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c120 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((334207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 524201/2500000) (δ := 523/100000000) (ψ := -16027/31250) 88 67
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t120 : ((15253236117/250000000000 : ℚ) : ℝ) ≤ stT88 120 := by
  have hc : ((167091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15253236117/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((167091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c121 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((89/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3922541/10000000) (δ := 483/100000000) (ψ := -16027/31250) 88 67
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t121 : ((15727257/100000000000 : ℚ) : ℝ) ≤ stT88 121 := by
  have hc : ((173/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15727257/100000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((173/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c122 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-132253/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22933/40000) (δ := 523/100000000) (ψ := -16027/31250) 88 67
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t122 : ((-59872682577/1000000000000 : ℚ) : ℝ) ≤ stT88 122 := by
  have hc : ((-132263/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59872682577/1000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-132263/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c123 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-247893/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7529179/10000000) (δ := 3/625000) (ψ := -16027/31250) 88 67
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t123 : ((-44705790437/500000000000 : ℚ) : ℝ) ≤ stT88 123 := by
  have hc : ((-495811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44705790437/500000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-495811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c124 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-835017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3198699/5000000) (δ := 57/10000000) (ψ := -16027/31250) 88 68
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t124 : ((-749912712809/10000000000000 : ℚ) : ℝ) ≤ stT88 124 := by
  have hc : ((-835067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-749912712809/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-835067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c125 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-69409/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4630321/10000000) (δ := 593/100000000) (ψ := -16027/31250) 88 68
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t125 : ((-31046266701/1250000000000 : ℚ) : ℝ) ≤ stT88 125 := by
  have hc : ((-138843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31046266701/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-138843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c126 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((407639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2877323/10000000) (δ := 833/100000000) (ψ := -16027/31250) 88 68
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t126 : ((36310881243/1000000000000 : ℚ) : ℝ) ≤ stT88 126 := by
  have hc : ((407589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36310881243/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((407589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c127 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((898141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142273/1250000) (δ := 73/10000000) (ψ := -16027/31250) 88 68
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t127 : ((199231609349/2500000000000 : ℚ) : ℝ) ≤ stT88 127 := by
  have hc : ((898091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199231609349/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((898091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c128 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((243133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117463/2000000) (δ := 53/10000000) (ψ := -16027/31250) 88 68
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t128 : ((429780153803/5000000000000 : ℚ) : ℝ) ≤ stT88 128 := by
  have hc : ((486241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429780153803/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((486241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c129 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((9469/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1149693/5000000) (δ := 873/100000000) (ψ := -16027/31250) 88 68
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t129 : ((5335227647/100000000000 : ℚ) : ℝ) ≤ stT88 129 := by
  have hc : ((302983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5335227647/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((302983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c130 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-14247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 999559/2500000) (δ := 473/100000000) (ψ := -16027/31250) 88 68
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t130 : ((-195584157/78125000000 : ℚ) : ℝ) ≤ stT88 130 := by
  have hc : ((-446/15625 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195584157/78125000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-446/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c131 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-32319/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1421017/2500000) (δ := 713/100000000) (ψ := -16027/31250) 88 68
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t131 : ((-11295782463/200000000000 : ℚ) : ℝ) ≤ stT88 131 := by
  have hc : ((-64643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11295782463/200000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-64643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c132 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-122539/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183927/250000) (δ := 713/100000000) (ψ := -16027/31250) 88 68
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t132 : ((-426648150409/5000000000000 : ℚ) : ℝ) ≤ stT88 132 := by
  have hc : ((-490181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426648150409/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-490181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c133 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-178729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3345249/5000000) (δ := 331/50000000) (ψ := -16027/31250) 88 69
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t133 : ((-15498637429/200000000000 : ℚ) : ℝ) ≤ stT88 133 := by
  have hc : ((-178739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15498637429/200000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-178739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c134 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-215781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100851/200000) (δ := 451/50000000) (ψ := -16027/31250) 88 69
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t134 : ((-93214056707/2500000000000 : ℚ) : ℝ) ≤ stT88 134 := by
  have hc : ((-107903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93214056707/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-107903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c135 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((206557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681371/2000000) (δ := 661/100000000) (ψ := -16027/31250) 88 69
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t135 : ((88866363817/5000000000000 : ℚ) : ℝ) ≤ stT88 135 := by
  have hc : ((206507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88866363817/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((206507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c136 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((189053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1783231/10000000) (δ := 741/100000000) (ψ := -16027/31250) 88 69
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t136 : ((81050358213/1250000000000 : ℚ) : ℝ) ≤ stT88 136 := by
  have hc : ((378081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81050358213/1250000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((378081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c137 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((62353/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85751/5000000) (δ := 331/50000000) (ψ := -16027/31250) 88 69
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t137 : ((426152417243/5000000000000 : ℚ) : ℝ) ≤ stT88 137 := by
  have hc : ((498799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426152417243/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((498799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c138 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((105143/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285701/2000000) (δ := 741/100000000) (ψ := -16027/31250) 88 69
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t138 : ((44749144629/625000000000 : ℚ) : ℝ) ≤ stT88 138 := by
  have hc : ((420547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44749144629/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((420547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c139 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((356027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3016959/10000000) (δ := 311/50000000) (ψ := -16027/31250) 88 69
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t139 : ((75483854919/2500000000000 : ℚ) : ℝ) ≤ stT88 139 := by
  have hc : ((355977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75483854919/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((355977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c140 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-13183/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4594027/10000000) (δ := 351/50000000) (ψ := -16027/31250) 88 69
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t140 : ((-4457516501/200000000000 : ℚ) : ℝ) ≤ stT88 140 := by
  have hc : ((-26371/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4457516501/200000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-26371/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c141 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-194763/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 615987/1000000) (δ := 781/100000000) (ψ := -16027/31250) 88 69
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t141 : ((-41007644219/625000000000 : ℚ) : ℝ) ≤ stT88 141 := by
  have hc : ((-389551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41007644219/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-389551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c142 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-998447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7714647/10000000) (δ := 501/100000000) (ψ := -16027/31250) 88 69
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t142 : ((-418960354727/5000000000000 : ℚ) : ℝ) ≤ stT88 142 := by
  have hc : ((-998497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418960354727/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-998497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c143 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-846291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6449451/10000000) (δ := 651/100000000) (ψ := -16027/31250) 88 70
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t143 : ((-707746736863/10000000000000 : ℚ) : ℝ) ≤ stT88 143 := by
  have hc : ((-846341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-707746736863/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-846341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c144 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-96373/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4916343/10000000) (δ := 109/12500000) (ψ := -16027/31250) 88 70
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t144 : ((-80321314257/2500000000000 : ℚ) : ℝ) ≤ stT88 144 := by
  have hc : ((-192771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80321314257/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-192771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c145 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((42329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1696923/5000000) (δ := 531/100000000) (ψ := -16027/31250) 88 70
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t145 : ((17571991413/1000000000000 : ℚ) : ℝ) ≤ stT88 145 := by
  have hc : ((42319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17571991413/1000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((42319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c146 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((729829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -470453/2500000) (δ := 691/100000000) (ψ := -16027/31250) 88 70
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t146 : ((120793749859/2000000000000 : ℚ) : ℝ) ≤ stT88 146 := by
  have hc : ((729779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120793749859/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((729779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c147 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((61779/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3801/100000) (δ := 47/6250000) (ψ := -16027/31250) 88 70
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t147 : ((203807507351/2500000000000 : ℚ) : ℝ) ≤ stT88 147 := by
  have hc : ((494207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203807507351/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((494207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c148 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((180559/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1111431/10000000) (δ := 79/12500000) (ψ := -16027/31250) 88 70
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t148 : ((74205097353/1000000000000 : ℚ) : ℝ) ≤ stT88 148 := by
  have hc : ((180549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74205097353/1000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((180549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c149 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((508661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296459/5000000) (δ := 851/100000000) (ψ := -16027/31250) 88 70
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t149 : ((416669898141/10000000000000 : ℚ) : ℝ) ≤ stT88 149 := by
  have hc : ((508611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416669898141/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((508611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c150 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-27487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 812899/2000000) (δ := 99/12500000) (ψ := -16027/31250) 88 70
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t150 : ((-2807933183/625000000000 : ℚ) : ℝ) ≤ stT88 150 := by
  have hc : ((-3439/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2807933183/625000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-3439/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c151 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-149243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1105259/2000000) (δ := 571/100000000) (ψ := -16027/31250) 88 70
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t151 : ((-242924968179/5000000000000 : ℚ) : ℝ) ≤ stT88 151 := by
  have hc : ((-298511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242924968179/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-298511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c152 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-939299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1395689/2000000) (δ := 731/100000000) (ψ := -16027/31250) 88 70
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t152 : ((-190478372173/2500000000000 : ℚ) : ℝ) ≤ stT88 152 := by
  have hc : ((-939349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190478372173/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-939349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c153 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-974383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -728689/1000000) (δ := 721/100000000) (ψ := -16027/31250) 88 71
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t153 : ((-787783282149/10000000000000 : ℚ) : ℝ) ≤ stT88 153 := by
  have hc : ((-974433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-787783282149/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-974433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c154 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-348307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -292683/500000) (δ := 881/100000000) (ψ := -16027/31250) 88 71
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t154 : ((-70173484309/1250000000000 : ℚ) : ℝ) ≤ stT88 154 := by
  have hc : ((-87083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70173484309/1250000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-87083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c155 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-99867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4429707/10000000) (δ := 761/100000000) (ψ := -16027/31250) 88 71
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t155 : ((-1002940653/62500000000 : ℚ) : ℝ) ≤ stT88 155 := by
  have hc : ((-24973/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1002940653/62500000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-24973/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c156 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((44599/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3014911/10000000) (δ := 841/100000000) (ψ := -16027/31250) 88 71
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t156 : ((223142121/7812500000 : ℚ) : ℝ) ≤ stT88 156 := by
  have hc : ((178371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223142121/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((178371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c157 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((799903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321831/2000000) (δ := 841/100000000) (ψ := -16027/31250) 88 71
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t157 : ((319175740679/5000000000000 : ℚ) : ℝ) ≤ stT88 157 := by
  have hc : ((799853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319175740679/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((799853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c158 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((249099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8493/400000) (δ := 601/100000000) (ψ := -16027/31250) 88 71
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t158 : ((396325017361/5000000000000 : ℚ) : ℝ) ≤ stT88 158 := by
  have hc : ((498173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((396325017361/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((498173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c159 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((891443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 293923/2500000) (δ := 881/100000000) (ψ := -16027/31250) 88 71
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t159 : ((706920110043/10000000000000 : ℚ) : ℝ) ≤ stT88 159 := by
  have hc : ((891393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((706920110043/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((891393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c160 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((260829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2555007/10000000) (δ := 761/100000000) (ψ := -16027/31250) 88 71
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t160 : ((51545889369/1250000000000 : ℚ) : ℝ) ≤ stT88 160 := by
  have hc : ((65201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51545889369/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((65201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c161 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((101/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122679/312500) (δ := 281/50000000) (ψ := -16027/31250) 88 71
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t161 : ((7171801/200000000000 : ℚ) : ℝ) ≤ stT88 161 := by
  have hc : ((91/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7171801/200000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((91/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c162 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-103579/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5287961/10000000) (δ := 601/100000000) (ψ := -16027/31250) 88 71
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t162 : ((-3255491503/80000000000 : ℚ) : ℝ) ≤ stT88 162 := by
  have hc : ((-103589/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3255491503/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-103589/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c163 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-884737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1660453/2500000) (δ := 881/100000000) (ψ := -16027/31250) 88 71
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t163 : ((-693019150407/10000000000000 : ℚ) : ℝ) ≤ stT88 163 := by
  have hc : ((-884787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-693019150407/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-884787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c164 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-998577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3860291/5000000) (δ := 67/10000000) (ψ := -16027/31250) 88 72
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t164 : ((-779796866863/10000000000000 : ℚ) : ℝ) ≤ stT88 164 := by
  have hc : ((-998627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-779796866863/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-998627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c165 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-207969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -797899/1250000) (δ := 613/100000000) (ψ := -16027/31250) 88 72
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t165 : ((-323826779537/5000000000000 : ℚ) : ℝ) ≤ stT88 165 := by
  have hc : ((-415963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323826779537/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-415963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c166 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-435647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2526941/5000000) (δ := 773/100000000) (ψ := -16027/31250) 88 72
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t166 : ((-338166662247/10000000000000 : ℚ) : ℝ) ≤ stT88 166 := by
  have hc : ((-435697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338166662247/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-435697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c167 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((15539/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3732557/10000000) (δ := 79/10000000) (ψ := -16027/31250) 88 72
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t167 : ((12016697367/2000000000000 : ℚ) : ℝ) ≤ stT88 167 := by
  have hc : ((15529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12016697367/2000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((15529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c168 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((283619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30239/125000) (δ := 693/100000000) (ψ := -16027/31250) 88 72
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t168 : ((27349663563/625000000000 : ℚ) : ℝ) ≤ stT88 168 := by
  have hc : ((141797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27349663563/625000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((141797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c169 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((451221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113479/10000000) (δ := 79/10000000) (ψ := -16027/31250) 88 72
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t169 : ((8676837477/125000000000 : ℚ) : ℝ) ≤ stT88 169 := by
  have hc : ((112799/125000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8676837477/125000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((112799/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c170 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((997279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9223/500000) (δ := 59/10000000) (ψ := -16027/31250) 88 72
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t170 : ((191209685689/2500000000000 : ℚ) : ℝ) ≤ stT88 170 := by
  have hc : ((997229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191209685689/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((997229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c171 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((207747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1474787/10000000) (δ := 493/100000000) (ψ := -16027/31250) 88 72
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t171 : ((317717038211/5000000000000 : ℚ) : ℝ) ≤ stT88 171 := by
  have hc : ((415469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317717038211/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((415469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c172 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((450889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2757589/10000000) (δ := 653/100000000) (ψ := -16027/31250) 88 72
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t172 : ((85940282697/2500000000000 : ℚ) : ℝ) ≤ stT88 172 := by
  have hc : ((450839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85940282697/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((450839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c173 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-42373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806591/2000000) (δ := 813/100000000) (ψ := -16027/31250) 88 72
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t173 : ((-16126806489/5000000000000 : ℚ) : ℝ) ≤ stT88 173 := by
  have hc : ((-42423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16126806489/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-42423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c174 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-522339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530097/1000000) (δ := 853/100000000) (ψ := -16027/31250) 88 72
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t174 : ((-396022578511/10000000000000 : ℚ) : ℝ) ≤ stT88 174 := by
  have hc : ((-522389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-396022578511/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-522389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c175 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-869353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3280859/5000000) (δ := 613/100000000) (ψ := -16027/31250) 88 72
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t175 : ((-657206940387/10000000000000 : ℚ) : ℝ) ≤ stT88 175 := by
  have hc : ((-869403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657206940387/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-869403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c176 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-24997/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7815283/10000000) (δ := 813/100000000) (ψ := -16027/31250) 88 72
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t176 : ((-75372623547/1000000000000 : ℚ) : ℝ) ≤ stT88 176 := by
  have hc : ((-99993/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75372623547/1000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-99993/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c177 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-885557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3323109/5000000) (δ := 619/100000000) (ψ := -16027/31250) 88 73
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t177 : ((-665663844729/10000000000000 : ℚ) : ℝ) ≤ stT88 177 := by
  have hc : ((-885607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-665663844729/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-885607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c178 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-557951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2703389/5000000) (δ := 459/100000000) (ψ := -16027/31250) 88 73
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t178 : ((-104559901383/2500000000000 : ℚ) : ℝ) ≤ stT88 178 := by
  have hc : ((-558001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104559901383/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-558001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c179 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-19751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2087141/5000000) (δ := 859/100000000) (ψ := -16027/31250) 88 73
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t179 : ((-3692520699/500000000000 : ℚ) : ℝ) ≤ stT88 179 := by
  have hc : ((-19761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3692520699/500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-19761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c180 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((381423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -737163/2500000) (δ := 459/100000000) (ψ := -16027/31250) 88 73
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t180 : ((56851654483/2000000000000 : ℚ) : ℝ) ≤ stT88 180 := by
  have hc : ((381373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56851654483/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((381373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c181 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((770019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -432453/2500000) (δ := 619/100000000) (ψ := -16027/31250) 88 73
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t181 : ((286156668943/5000000000000 : ℚ) : ℝ) ≤ stT88 181 := by
  have hc : ((769969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286156668943/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((769969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c182 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((244659/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64711/1250000) (δ := 93/12500000) (ψ := -16027/31250) 88 73
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t182 : ((362687946957/5000000000000 : ℚ) : ℝ) ≤ stT88 182 := by
  have hc : ((489293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362687946957/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((489293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c183 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((962393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137559/2000000) (δ := 29/6250000) (ψ := -16027/31250) 88 73
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t183 : ((711384154803/10000000000000 : ℚ) : ℝ) ≤ stT88 183 := by
  have hc : ((962343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((711384154803/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((962343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c184 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((728489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 471677/2500000) (δ := 63/12500000) (ψ := -16027/31250) 88 73
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t184 : ((537011786751/10000000000000 : ℚ) : ℝ) ≤ stT88 184 := by
  have hc : ((728439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537011786751/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((728439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c185 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((332683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1539561/5000000) (δ := 699/100000000) (ψ := -16027/31250) 88 73
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t185 : ((122278219231/5000000000000 : ℚ) : ℝ) ≤ stT88 185 := by
  have hc : ((332633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122278219231/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((332633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c186 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-26967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4265109/10000000) (δ := 39/6250000) (ψ := -16027/31250) 88 73
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t186 : ((-4945126893/500000000000 : ℚ) : ℝ) ≤ stT88 186 := by
  have hc : ((-26977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4945126893/500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-26977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c187 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-570487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5444737/10000000) (δ := 739/100000000) (ψ := -16027/31250) 88 73
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t187 : ((-417218303601/10000000000000 : ℚ) : ℝ) ≤ stT88 187 := by
  have hc : ((-570537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-417218303601/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-570537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c188 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-880271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6618073/10000000) (δ := 17/3125000) (ψ := -16027/31250) 88 73
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t188 : ((-25681604533/400000000000 : ℚ) : ℝ) ≤ stT88 188 := by
  have hc : ((-880321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25681604533/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-880321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c189 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-999621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243287/312500) (δ := 779/100000000) (ψ := -16027/31250) 88 73
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t189 : ((-727153687703/10000000000000 : ℚ) : ℝ) ≤ stT88 189 := by
  have hc : ((-999671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-727153687703/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-999671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c190 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-226521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3380913/5000000) (δ := 127/20000000) (ψ := -16027/31250) 88 74
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t190 : ((-328689687959/5000000000000 : ℚ) : ℝ) ≤ stT88 190 := by
  have hc : ((-453067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-328689687959/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-453067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c191 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-124509/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -700871/1250000) (δ := 81/12500000) (ψ := -16027/31250) 88 74
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t191 : ((-3603953417/80000000000 : ℚ) : ℝ) ≤ stT88 191 := by
  have hc : ((-124519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3603953417/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-124519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c192 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-42173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222907/500000) (δ := 127/20000000) (ψ := -16027/31250) 88 74
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t192 : ((-3805370613/250000000000 : ℚ) : ℝ) ≤ stT88 192 := by
  have hc : ((-42183/200000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3805370613/250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-42183/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c193 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((969/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3315281/10000000) (δ := 151/20000000) (ψ := -16027/31250) 88 74
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t193 : ((174339193/10000000000 : ℚ) : ℝ) ≤ stT88 193 := by
  have hc : ((1211/5000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174339193/10000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((1211/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c194 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((643809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2178327/10000000) (δ := 103/20000000) (ψ := -16027/31250) 88 74
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t194 : ((231095962061/5000000000000 : ℚ) : ℝ) ≤ stT88 194 := by
  have hc : ((643759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231095962061/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((643759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c195 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((456771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1047219/10000000) (δ := 103/20000000) (ψ := -16027/31250) 88 74
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t195 : ((81770551261/1250000000000 : ℚ) : ℝ) ≤ stT88 195 := by
  have hc : ((228373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81770551261/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((228373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c196 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((124939/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78103/10000000) (δ := 103/20000000) (ψ := -16027/31250) 88 74
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t196 : ((71390071467/1000000000000 : ℚ) : ℝ) ≤ stT88 196 := by
  have hc : ((499731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71390071467/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((499731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c197 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((44371/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 598849/5000000) (δ := 81/12500000) (ψ := -16027/31250) 88 74
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t197 : ((6322245039/100000000000 : ℚ) : ℝ) ≤ stT88 197 := by
  have hc : ((88737/100000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6322245039/100000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((88737/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c198 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((301057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288953/1250000) (δ := 81/12500000) (ψ := -16027/31250) 88 74
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t198 : ((26741763801/625000000000 : ℚ) : ℝ) ≤ stT88 198 := by
  have hc : ((37629/62500 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26741763801/625000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((37629/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c199 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((201433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3419939/10000000) (δ := 43/6250000) (ψ := -16027/31250) 88 74
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t199 : ((142756582423/10000000000000 : ℚ) : ℝ) ≤ stT88 199 := by
  have hc : ((201383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142756582423/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((201383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_c200 :
    |Real.cos (((88 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((-118017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2261349/5000000) (δ := 111/20000000) (ψ := -16027/31250) 88 74
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st88_t200 : ((-41734162247/2500000000000 : ℚ) : ℝ) ≤ stT88 200 := by
  have hc : ((-59021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((88 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-16027/31250 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st88_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41734162247/2500000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-59021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st88_p1 : ((871293/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT88 (i+1) := by
  rw [Finset.sum_range_one]
  exact st88_t1

theorem st88_p2 : ((10453480213117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT88 (i+1))
      = (∑ i ∈ Finset.range 1, stT88 (i+1)) + stT88 2 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 1
    simpa using h
  have hprev := st88_p1
  have hstep := st88_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p3 : ((4793207153953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT88 (i+1))
      = (∑ i ∈ Finset.range 2, stT88 (i+1)) + stT88 3 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 2
    simpa using h
  have hprev := st88_p2
  have hstep := st88_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p4 : ((-206453845979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT88 (i+1))
      = (∑ i ∈ Finset.range 3, stT88 (i+1)) + stT88 4 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 3
    simpa using h
  have hprev := st88_p3
  have hstep := st88_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p5 : ((-3411879684659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT88 (i+1))
      = (∑ i ∈ Finset.range 4, stT88 (i+1)) + stT88 5 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 4
    simpa using h
  have hprev := st88_p4
  have hstep := st88_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p6 : ((-1589688338851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT88 (i+1))
      = (∑ i ∈ Finset.range 5, stT88 (i+1)) + stT88 6 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 5
    simpa using h
  have hprev := st88_p5
  have hstep := st88_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p7 : ((-3520656054321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT88 (i+1))
      = (∑ i ∈ Finset.range 6, stT88 (i+1)) + stT88 7 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 6
    simpa using h
  have hprev := st88_p6
  have hstep := st88_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p8 : ((-2545633834647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT88 (i+1))
      = (∑ i ∈ Finset.range 7, stT88 (i+1)) + stT88 8 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 7
    simpa using h
  have hprev := st88_p7
  have hstep := st88_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p9 : ((-62536338231/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT88 (i+1))
      = (∑ i ∈ Finset.range 8, stT88 (i+1)) + stT88 9 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 8
    simpa using h
  have hprev := st88_p8
  have hstep := st88_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p10 : ((-101882240233/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT88 (i+1))
      = (∑ i ∈ Finset.range 9, stT88 (i+1)) + stT88 10 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 9
    simpa using h
  have hprev := st88_p9
  have hstep := st88_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p11 : ((-35616643271/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT88 (i+1))
      = (∑ i ∈ Finset.range 10, stT88 (i+1)) + stT88 11 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 10
    simpa using h
  have hprev := st88_p10
  have hstep := st88_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p12 : ((-140459737737/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT88 (i+1))
      = (∑ i ∈ Finset.range 11, stT88 (i+1)) + stT88 12 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 11
    simpa using h
  have hprev := st88_p11
  have hstep := st88_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p13 : ((136718582613/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT88 (i+1))
      = (∑ i ∈ Finset.range 12, stT88 (i+1)) + stT88 13 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 12
    simpa using h
  have hprev := st88_p12
  have hstep := st88_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p14 : ((1970684099391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT88 (i+1))
      = (∑ i ∈ Finset.range 13, stT88 (i+1)) + stT88 14 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 13
    simpa using h
  have hprev := st88_p13
  have hstep := st88_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p15 : ((130370867463/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT88 (i+1))
      = (∑ i ∈ Finset.range 14, stT88 (i+1)) + stT88 15 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 14
    simpa using h
  have hprev := st88_p14
  have hstep := st88_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p16 : ((173162117463/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT88 (i+1))
      = (∑ i ∈ Finset.range 15, stT88 (i+1)) + stT88 16 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 15
    simpa using h
  have hprev := st88_p15
  have hstep := st88_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p17 : ((884944220799/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT88 (i+1))
      = (∑ i ∈ Finset.range 16, stT88 (i+1)) + stT88 17 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 16
    simpa using h
  have hprev := st88_p16
  have hstep := st88_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p18 : ((667522991187/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT88 (i+1))
      = (∑ i ∈ Finset.range 17, stT88 (i+1)) + stT88 18 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 17
    simpa using h
  have hprev := st88_p17
  have hstep := st88_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p19 : ((355849058713/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT88 (i+1))
      = (∑ i ∈ Finset.range 18, stT88 (i+1)) + stT88 19 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 18
    simpa using h
  have hprev := st88_p18
  have hstep := st88_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p20 : ((7863564979223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT88 (i+1))
      = (∑ i ∈ Finset.range 19, stT88 (i+1)) + stT88 20 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 19
    simpa using h
  have hprev := st88_p19
  have hstep := st88_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p21 : ((149656062241/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT88 (i+1))
      = (∑ i ∈ Finset.range 20, stT88 (i+1)) + stT88 21 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 20
    simpa using h
  have hprev := st88_p20
  have hstep := st88_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p22 : ((2994051735721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT88 (i+1))
      = (∑ i ∈ Finset.range 21, stT88 (i+1)) + stT88 22 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 21
    simpa using h
  have hprev := st88_p21
  have hstep := st88_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p23 : ((807255311849/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT88 (i+1))
      = (∑ i ∈ Finset.range 22, stT88 (i+1)) + stT88 23 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 22
    simpa using h
  have hprev := st88_p22
  have hstep := st88_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p24 : ((3182433195613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT88 (i+1))
      = (∑ i ∈ Finset.range 23, stT88 (i+1)) + stT88 24 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 23
    simpa using h
  have hprev := st88_p23
  have hstep := st88_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p25 : ((3696689195613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT88 (i+1))
      = (∑ i ∈ Finset.range 24, stT88 (i+1)) + stT88 25 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 24
    simpa using h
  have hprev := st88_p24
  have hstep := st88_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p26 : ((3472738223347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT88 (i+1))
      = (∑ i ∈ Finset.range 25, stT88 (i+1)) + stT88 26 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 25
    simpa using h
  have hprev := st88_p25
  have hstep := st88_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p27 : ((3521562788347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT88 (i+1))
      = (∑ i ∈ Finset.range 26, stT88 (i+1)) + stT88 27 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 26
    simpa using h
  have hprev := st88_p26
  have hstep := st88_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p28 : ((1764512375257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT88 (i+1))
      = (∑ i ∈ Finset.range 27, stT88 (i+1)) + stT88 28 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 27
    simpa using h
  have hprev := st88_p27
  have hstep := st88_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p29 : ((7142620711507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT88 (i+1))
      = (∑ i ∈ Finset.range 28, stT88 (i+1)) + stT88 29 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 28
    simpa using h
  have hprev := st88_p28
  have hstep := st88_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p30 : ((1354579400411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT88 (i+1))
      = (∑ i ∈ Finset.range 29, stT88 (i+1)) + stT88 30 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 29
    simpa using h
  have hprev := st88_p29
  have hstep := st88_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p31 : ((7570085902423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT88 (i+1))
      = (∑ i ∈ Finset.range 30, stT88 (i+1)) + stT88 31 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 30
    simpa using h
  have hprev := st88_p30
  have hstep := st88_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p32 : ((6292481800649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT88 (i+1))
      = (∑ i ∈ Finset.range 31, stT88 (i+1)) + stT88 32 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 31
    simpa using h
  have hprev := st88_p31
  have hstep := st88_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p33 : ((1587910713869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT88 (i+1))
      = (∑ i ∈ Finset.range 32, stT88 (i+1)) + stT88 33 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 32
    simpa using h
  have hprev := st88_p32
  have hstep := st88_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p34 : ((6253772065939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT88 (i+1))
      = (∑ i ∈ Finset.range 33, stT88 (i+1)) + stT88 34 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 33
    simpa using h
  have hprev := st88_p33
  have hstep := st88_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p35 : ((7460366315887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT88 (i+1))
      = (∑ i ∈ Finset.range 34, stT88 (i+1)) + stT88 35 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 34
    simpa using h
  have hprev := st88_p34
  have hstep := st88_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p36 : ((7240146271843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT88 (i+1))
      = (∑ i ∈ Finset.range 35, stT88 (i+1)) + stT88 36 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 35
    simpa using h
  have hprev := st88_p35
  have hstep := st88_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p37 : ((6314494414363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT88 (i+1))
      = (∑ i ∈ Finset.range 36, stT88 (i+1)) + stT88 37 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 36
    simpa using h
  have hprev := st88_p36
  have hstep := st88_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p38 : ((7910997944677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT88 (i+1))
      = (∑ i ∈ Finset.range 37, stT88 (i+1)) + stT88 38 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 37
    simpa using h
  have hprev := st88_p37
  have hstep := st88_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p39 : ((6663546424371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT88 (i+1))
      = (∑ i ∈ Finset.range 38, stT88 (i+1)) + stT88 39 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 38
    simpa using h
  have hprev := st88_p38
  have hstep := st88_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p40 : ((828865347923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT88 (i+1))
      = (∑ i ∈ Finset.range 39, stT88 (i+1)) + stT88 40 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 39
    simpa using h
  have hprev := st88_p39
  have hstep := st88_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p41 : ((7935833695471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT88 (i+1))
      = (∑ i ∈ Finset.range 40, stT88 (i+1)) + stT88 41 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 40
    simpa using h
  have hprev := st88_p40
  have hstep := st88_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p42 : ((6539324661077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT88 (i+1))
      = (∑ i ∈ Finset.range 41, stT88 (i+1)) + stT88 42 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 41
    simpa using h
  have hprev := st88_p41
  have hstep := st88_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p43 : ((6631375805647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT88 (i+1))
      = (∑ i ∈ Finset.range 42, stT88 (i+1)) + stT88 43 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 42
    simpa using h
  have hprev := st88_p42
  have hstep := st88_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p44 : ((1588999357339/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT88 (i+1))
      = (∑ i ∈ Finset.range 43, stT88 (i+1)) + stT88 44 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 43
    simpa using h
  have hprev := st88_p43
  have hstep := st88_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p45 : ((6759320238983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT88 (i+1))
      = (∑ i ∈ Finset.range 44, stT88 (i+1)) + stT88 45 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 44
    simpa using h
  have hprev := st88_p44
  have hstep := st88_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p46 : ((6340595279923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT88 (i+1))
      = (∑ i ∈ Finset.range 45, stT88 (i+1)) + stT88 46 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 45
    simpa using h
  have hprev := st88_p45
  have hstep := st88_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p47 : ((1949583885399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT88 (i+1))
      = (∑ i ∈ Finset.range 46, stT88 (i+1)) + stT88 47 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 46
    simpa using h
  have hprev := st88_p46
  have hstep := st88_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p48 : ((1837513316723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT88 (i+1))
      = (∑ i ∈ Finset.range 47, stT88 (i+1)) + stT88 48 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 47
    simpa using h
  have hprev := st88_p47
  have hstep := st88_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p49 : ((191849997669/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT88 (i+1))
      = (∑ i ∈ Finset.range 48, stT88 (i+1)) + stT88 49 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 48
    simpa using h
  have hprev := st88_p48
  have hstep := st88_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p50 : ((7120045736327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT88 (i+1))
      = (∑ i ∈ Finset.range 49, stT88 (i+1)) + stT88 50 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 49
    simpa using h
  have hprev := st88_p49
  have hstep := st88_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p51 : ((7947734440967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT88 (i+1))
      = (∑ i ∈ Finset.range 50, stT88 (i+1)) + stT88 51 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 50
    simpa using h
  have hprev := st88_p50
  have hstep := st88_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p52 : ((1681755131237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT88 (i+1))
      = (∑ i ∈ Finset.range 51, stT88 (i+1)) + stT88 52 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 51
    simpa using h
  have hprev := st88_p51
  have hstep := st88_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p53 : ((1551489206227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT88 (i+1))
      = (∑ i ∈ Finset.range 52, stT88 (i+1)) + stT88 53 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 52
    simpa using h
  have hprev := st88_p52
  have hstep := st88_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p54 : ((937474129169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT88 (i+1))
      = (∑ i ∈ Finset.range 53, stT88 (i+1)) + stT88 54 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 53
    simpa using h
  have hprev := st88_p53
  have hstep := st88_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p55 : ((7860671799717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT88 (i+1))
      = (∑ i ∈ Finset.range 54, stT88 (i+1)) + stT88 55 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 54
    simpa using h
  have hprev := st88_p54
  have hstep := st88_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p56 : ((656790034547/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT88 (i+1))
      = (∑ i ∈ Finset.range 55, stT88 (i+1)) + stT88 56 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 55
    simpa using h
  have hprev := st88_p55
  have hstep := st88_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p57 : ((1553829402017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT88 (i+1))
      = (∑ i ∈ Finset.range 56, stT88 (i+1)) + stT88 57 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 56
    simpa using h
  have hprev := st88_p56
  have hstep := st88_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p58 : ((1866460420703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT88 (i+1))
      = (∑ i ∈ Finset.range 57, stT88 (i+1)) + stT88 58 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 57
    simpa using h
  have hprev := st88_p57
  have hstep := st88_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p59 : ((7944076286183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT88 (i+1))
      = (∑ i ∈ Finset.range 58, stT88 (i+1)) + stT88 59 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 58
    simpa using h
  have hprev := st88_p58
  have hstep := st88_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p60 : ((6791816772863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT88 (i+1))
      = (∑ i ∈ Finset.range 59, stT88 (i+1)) + stT88 60 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 59
    simpa using h
  have hprev := st88_p59
  have hstep := st88_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p61 : ((1217120216559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT88 (i+1))
      = (∑ i ∈ Finset.range 60, stT88 (i+1)) + stT88 61 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 60
    simpa using h
  have hprev := st88_p60
  have hstep := st88_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p62 : ((7036925811869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT88 (i+1))
      = (∑ i ∈ Finset.range 61, stT88 (i+1)) + stT88 62 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 61
    simpa using h
  have hprev := st88_p61
  have hstep := st88_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p63 : ((62604355661/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT88 (i+1))
      = (∑ i ∈ Finset.range 62, stT88 (i+1)) + stT88 63 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 62
    simpa using h
  have hprev := st88_p62
  have hstep := st88_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p64 : ((7415075795983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT88 (i+1))
      = (∑ i ∈ Finset.range 63, stT88 (i+1)) + stT88 64 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 63
    simpa using h
  have hprev := st88_p63
  have hstep := st88_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p65 : ((249095421199/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT88 (i+1))
      = (∑ i ∈ Finset.range 64, stT88 (i+1)) + stT88 65 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 64
    simpa using h
  have hprev := st88_p64
  have hstep := st88_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p66 : ((6307700206647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT88 (i+1))
      = (∑ i ∈ Finset.range 65, stT88 (i+1)) + stT88 66 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 65
    simpa using h
  have hprev := st88_p65
  have hstep := st88_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p67 : ((300365149863/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT88 (i+1))
      = (∑ i ∈ Finset.range 66, stT88 (i+1)) + stT88 67 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 66
    simpa using h
  have hprev := st88_p66
  have hstep := st88_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p68 : ((8035654131327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT88 (i+1))
      = (∑ i ∈ Finset.range 67, stT88 (i+1)) + stT88 68 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 67
    simpa using h
  have hprev := st88_p67
  have hstep := st88_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p69 : ((3571383780597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT88 (i+1))
      = (∑ i ∈ Finset.range 68, stT88 (i+1)) + stT88 69 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 68
    simpa using h
  have hprev := st88_p68
  have hstep := st88_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p70 : ((3056005816713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT88 (i+1))
      = (∑ i ∈ Finset.range 69, stT88 (i+1)) + stT88 70 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 69
    simpa using h
  have hprev := st88_p69
  have hstep := st88_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p71 : ((3178728466361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT88 (i+1))
      = (∑ i ∈ Finset.range 70, stT88 (i+1)) + stT88 71 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 70
    simpa using h
  have hprev := st88_p70
  have hstep := st88_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p72 : ((752571253/1000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT88 (i+1))
      = (∑ i ∈ Finset.range 71, stT88 (i+1)) + stT88 72 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 71
    simpa using h
  have hprev := st88_p71
  have hstep := st88_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p73 : ((4037527148069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT88 (i+1))
      = (∑ i ∈ Finset.range 72, stT88 (i+1)) + stT88 73 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 72
    simpa using h
  have hprev := st88_p72
  have hstep := st88_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p74 : ((3659210633189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT88 (i+1))
      = (∑ i ∈ Finset.range 73, stT88 (i+1)) + stT88 74 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 73
    simpa using h
  have hprev := st88_p73
  have hstep := st88_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p75 : ((1555489114153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT88 (i+1))
      = (∑ i ∈ Finset.range 74, stT88 (i+1)) + stT88 75 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 74
    simpa using h
  have hprev := st88_p74
  have hstep := st88_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p76 : ((244929874697/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT88 (i+1))
      = (∑ i ∈ Finset.range 75, stT88 (i+1)) + stT88 76 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 75
    simpa using h
  have hprev := st88_p75
  have hstep := st88_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p77 : ((355983993623/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT88 (i+1))
      = (∑ i ∈ Finset.range 76, stT88 (i+1)) + stT88 77 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 76
    simpa using h
  have hprev := st88_p76
  have hstep := st88_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p78 : ((8035242451491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT88 (i+1))
      = (∑ i ∈ Finset.range 77, stT88 (i+1)) + stT88 78 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 77
    simpa using h
  have hprev := st88_p77
  have hstep := st88_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p79 : ((7834675263907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT88 (i+1))
      = (∑ i ∈ Finset.range 78, stT88 (i+1)) + stT88 79 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 78
    simpa using h
  have hprev := st88_p78
  have hstep := st88_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p80 : ((6761587348741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT88 (i+1))
      = (∑ i ∈ Finset.range 79, stT88 (i+1)) + stT88 80 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 79
    simpa using h
  have hprev := st88_p79
  have hstep := st88_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p81 : ((5994210068173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT88 (i+1))
      = (∑ i ∈ Finset.range 80, stT88 (i+1)) + stT88 81 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 80
    simpa using h
  have hprev := st88_p80
  have hstep := st88_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p82 : ((1584719179627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT88 (i+1))
      = (∑ i ∈ Finset.range 81, stT88 (i+1)) + stT88 82 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 81
    simpa using h
  have hprev := st88_p81
  have hstep := st88_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p83 : ((741739889251/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT88 (i+1))
      = (∑ i ∈ Finset.range 82, stT88 (i+1)) + stT88 83 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 82
    simpa using h
  have hprev := st88_p82
  have hstep := st88_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p84 : ((1015399499787/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT88 (i+1))
      = (∑ i ∈ Finset.range 83, stT88 (i+1)) + stT88 84 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 83
    simpa using h
  have hprev := st88_p83
  have hstep := st88_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p85 : ((3881791817379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT88 (i+1))
      = (∑ i ∈ Finset.range 84, stT88 (i+1)) + stT88 85 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 84
    simpa using h
  have hprev := st88_p84
  have hstep := st88_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p86 : ((3353743222403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT88 (i+1))
      = (∑ i ∈ Finset.range 85, stT88 (i+1)) + stT88 86 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 85
    simpa using h
  have hprev := st88_p85
  have hstep := st88_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p87 : ((1492772119237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT88 (i+1))
      = (∑ i ∈ Finset.range 86, stT88 (i+1)) + stT88 87 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 86
    simpa using h
  have hprev := st88_p86
  have hstep := st88_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p88 : ((3116674333507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT88 (i+1))
      = (∑ i ∈ Finset.range 87, stT88 (i+1)) + stT88 88 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 87
    simpa using h
  have hprev := st88_p87
  have hstep := st88_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p89 : ((3618423913457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT88 (i+1))
      = (∑ i ∈ Finset.range 88, stT88 (i+1)) + stT88 89 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 88
    simpa using h
  have hprev := st88_p88
  have hstep := st88_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p90 : ((4036229089037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT88 (i+1))
      = (∑ i ∈ Finset.range 89, stT88 (i+1)) + stT88 90 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 89
    simpa using h
  have hprev := st88_p89
  have hstep := st88_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p91 : ((8012654567109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT88 (i+1))
      = (∑ i ∈ Finset.range 90, stT88 (i+1)) + stT88 91 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 90
    simpa using h
  have hprev := st88_p90
  have hstep := st88_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p92 : ((712487967843/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT88 (i+1))
      = (∑ i ∈ Finset.range 91, stT88 (i+1)) + stT88 92 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 91
    simpa using h
  have hprev := st88_p91
  have hstep := st88_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p93 : ((3084735236427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT88 (i+1))
      = (∑ i ∈ Finset.range 92, stT88 (i+1)) + stT88 93 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 92
    simpa using h
  have hprev := st88_p92
  have hstep := st88_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p94 : ((2967008729347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT88 (i+1))
      = (∑ i ∈ Finset.range 93, stT88 (i+1)) + stT88 94 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 93
    simpa using h
  have hprev := st88_p93
  have hstep := st88_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p95 : ((329783892637/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT88 (i+1))
      = (∑ i ∈ Finset.range 94, stT88 (i+1)) + stT88 95 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 94
    simpa using h
  have hprev := st88_p94
  have hstep := st88_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p96 : ((95186079191/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT88 (i+1))
      = (∑ i ∈ Finset.range 95, stT88 (i+1)) + stT88 96 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 95
    simpa using h
  have hprev := st88_p95
  have hstep := st88_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p97 : ((4097091428733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT88 (i+1))
      = (∑ i ∈ Finset.range 96, stT88 (i+1)) + stT88 97 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 96
    simpa using h
  have hprev := st88_p96
  have hstep := st88_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p98 : ((7900106105953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT88 (i+1))
      = (∑ i ∈ Finset.range 97, stT88 (i+1)) + stT88 98 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 97
    simpa using h
  have hprev := st88_p97
  have hstep := st88_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p99 : ((6967476068663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT88 (i+1))
      = (∑ i ∈ Finset.range 98, stT88 (i+1)) + stT88 99 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 98
    simpa using h
  have hprev := st88_p98
  have hstep := st88_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p100 : ((6090991068663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT88 (i+1))
      = (∑ i ∈ Finset.range 99, stT88 (i+1)) + stT88 100 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 99
    simpa using h
  have hprev := st88_p99
  have hstep := st88_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p101 : ((5900304971457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT88 (i+1))
      = (∑ i ∈ Finset.range 100, stT88 (i+1)) + stT88 101 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 100
    simpa using h
  have hprev := st88_p100
  have hstep := st88_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p102 : ((6518394334737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT88 (i+1))
      = (∑ i ∈ Finset.range 101, stT88 (i+1)) + stT88 102 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 101
    simpa using h
  have hprev := st88_p101
  have hstep := st88_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p103 : ((375148083771/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT88 (i+1))
      = (∑ i ∈ Finset.range 102, stT88 (i+1)) + stT88 103 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 102
    simpa using h
  have hprev := st88_p102
  have hstep := st88_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p104 : ((408872191131/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT88 (i+1))
      = (∑ i ∈ Finset.range 103, stT88 (i+1)) + stT88 104 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 103
    simpa using h
  have hprev := st88_p103
  have hstep := st88_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p105 : ((4047984875867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT88 (i+1))
      = (∑ i ∈ Finset.range 104, stT88 (i+1)) + stT88 105 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 104
    simpa using h
  have hprev := st88_p104
  have hstep := st88_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p106 : ((732454138681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT88 (i+1))
      = (∑ i ∈ Finset.range 105, stT88 (i+1)) + stT88 106 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 105
    simpa using h
  have hprev := st88_p105
  have hstep := st88_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p107 : ((1274442720359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT88 (i+1))
      = (∑ i ∈ Finset.range 106, stT88 (i+1)) + stT88 107 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 106
    simpa using h
  have hprev := st88_p106
  have hstep := st88_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p108 : ((5845615968539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT88 (i+1))
      = (∑ i ∈ Finset.range 107, stT88 (i+1)) + stT88 108 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 107
    simpa using h
  have hprev := st88_p107
  have hstep := st88_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p109 : ((6065836448981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT88 (i+1))
      = (∑ i ∈ Finset.range 108, stT88 (i+1)) + stT88 109 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 108
    simpa using h
  have hprev := st88_p108
  have hstep := st88_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p110 : ((6885975857521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT88 (i+1))
      = (∑ i ∈ Finset.range 109, stT88 (i+1)) + stT88 110 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 109
    simpa using h
  have hprev := st88_p109
  have hstep := st88_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p111 : ((390143408181/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT88 (i+1))
      = (∑ i ∈ Finset.range 110, stT88 (i+1)) + stT88 111 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 110
    simpa using h
  have hprev := st88_p110
  have hstep := st88_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p112 : ((8272542790547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT88 (i+1))
      = (∑ i ∈ Finset.range 111, stT88 (i+1)) + stT88 112 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 111
    simpa using h
  have hprev := st88_p111
  have hstep := st88_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p113 : ((4014434385319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT88 (i+1))
      = (∑ i ∈ Finset.range 112, stT88 (i+1)) + stT88 113 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 112
    simpa using h
  have hprev := st88_p112
  have hstep := st88_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p114 : ((1805597153707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT88 (i+1))
      = (∑ i ∈ Finset.range 113, stT88 (i+1)) + stT88 114 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 113
    simpa using h
  have hprev := st88_p113
  have hstep := st88_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p115 : ((789435342761/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT88 (i+1))
      = (∑ i ∈ Finset.range 114, stT88 (i+1)) + stT88 115 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 114
    simpa using h
  have hprev := st88_p114
  have hstep := st88_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p116 : ((5811419078127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT88 (i+1))
      = (∑ i ∈ Finset.range 115, stT88 (i+1)) + stT88 116 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 115
    simpa using h
  have hprev := st88_p115
  have hstep := st88_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p117 : ((5978295950627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT88 (i+1))
      = (∑ i ∈ Finset.range 116, stT88 (i+1)) + stT88 117 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 116
    simpa using h
  have hprev := st88_p116
  have hstep := st88_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p118 : ((6716471100563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT88 (i+1))
      = (∑ i ∈ Finset.range 117, stT88 (i+1)) + stT88 118 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 117
    simpa using h
  have hprev := st88_p117
  have hstep := st88_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p119 : ((7628328935123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT88 (i+1))
      = (∑ i ∈ Finset.range 118, stT88 (i+1)) + stT88 119 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 118
    simpa using h
  have hprev := st88_p118
  have hstep := st88_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p120 : ((8238458379803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT88 (i+1))
      = (∑ i ∈ Finset.range 119, stT88 (i+1)) + stT88 120 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 119
    simpa using h
  have hprev := st88_p119
  have hstep := st88_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p121 : ((8240031105503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT88 (i+1))
      = (∑ i ∈ Finset.range 120, stT88 (i+1)) + stT88 121 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 120
    simpa using h
  have hprev := st88_p120
  have hstep := st88_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p122 : ((7641304279733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT88 (i+1))
      = (∑ i ∈ Finset.range 121, stT88 (i+1)) + stT88 122 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 121
    simpa using h
  have hprev := st88_p121
  have hstep := st88_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p123 : ((6747188470993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT88 (i+1))
      = (∑ i ∈ Finset.range 122, stT88 (i+1)) + stT88 123 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 122
    simpa using h
  have hprev := st88_p122
  have hstep := st88_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p124 : ((749659469773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT88 (i+1))
      = (∑ i ∈ Finset.range 123, stT88 (i+1)) + stT88 124 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 123
    simpa using h
  have hprev := st88_p123
  have hstep := st88_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p125 : ((5614165649/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT88 (i+1))
      = (∑ i ∈ Finset.range 124, stT88 (i+1)) + stT88 125 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 124
    simpa using h
  have hprev := st88_p124
  have hstep := st88_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p126 : ((3056007218503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT88 (i+1))
      = (∑ i ∈ Finset.range 125, stT88 (i+1)) + stT88 126 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 125
    simpa using h
  have hprev := st88_p125
  have hstep := st88_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p127 : ((3454470437201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT88 (i+1))
      = (∑ i ∈ Finset.range 126, stT88 (i+1)) + stT88 127 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 126
    simpa using h
  have hprev := st88_p126
  have hstep := st88_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p128 : ((971062647751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT88 (i+1))
      = (∑ i ∈ Finset.range 127, stT88 (i+1)) + stT88 128 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 127
    simpa using h
  have hprev := st88_p127
  have hstep := st88_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p129 : ((2075505986677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT88 (i+1))
      = (∑ i ∈ Finset.range 128, stT88 (i+1)) + stT88 129 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 128
    simpa using h
  have hprev := st88_p128
  have hstep := st88_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p130 : ((2069247293653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT88 (i+1))
      = (∑ i ∈ Finset.range 129, stT88 (i+1)) + stT88 130 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 129
    simpa using h
  have hprev := st88_p129
  have hstep := st88_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p131 : ((3856100025731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT88 (i+1))
      = (∑ i ∈ Finset.range 130, stT88 (i+1)) + stT88 131 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 130
    simpa using h
  have hprev := st88_p130
  have hstep := st88_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p132 : ((1714725937661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT88 (i+1))
      = (∑ i ∈ Finset.range 131, stT88 (i+1)) + stT88 132 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 131
    simpa using h
  have hprev := st88_p131
  have hstep := st88_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p133 : ((3041985939597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT88 (i+1))
      = (∑ i ∈ Finset.range 132, stT88 (i+1)) + stT88 133 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 132
    simpa using h
  have hprev := st88_p132
  have hstep := st88_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p134 : ((2855557826183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT88 (i+1))
      = (∑ i ∈ Finset.range 133, stT88 (i+1)) + stT88 134 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 133
    simpa using h
  have hprev := st88_p133
  have hstep := st88_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p135 : ((294442419/500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT88 (i+1))
      = (∑ i ∈ Finset.range 134, stT88 (i+1)) + stT88 135 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 134
    simpa using h
  have hprev := st88_p134
  have hstep := st88_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p136 : ((817156405713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT88 (i+1))
      = (∑ i ∈ Finset.range 135, stT88 (i+1)) + stT88 136 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 135
    simpa using h
  have hprev := st88_p135
  have hstep := st88_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p137 : ((738955608019/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT88 (i+1))
      = (∑ i ∈ Finset.range 136, stT88 (i+1)) + stT88 137 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 136
    simpa using h
  have hprev := st88_p136
  have hstep := st88_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p138 : ((4052771197127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT88 (i+1))
      = (∑ i ∈ Finset.range 137, stT88 (i+1)) + stT88 138 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 137
    simpa using h
  have hprev := st88_p137
  have hstep := st88_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p139 : ((840747781393/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT88 (i+1))
      = (∑ i ∈ Finset.range 138, stT88 (i+1)) + stT88 139 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 138
    simpa using h
  have hprev := st88_p138
  have hstep := st88_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p140 : ((102307524861/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT88 (i+1))
      = (∑ i ∈ Finset.range 139, stT88 (i+1)) + stT88 140 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 139
    simpa using h
  have hprev := st88_p139
  have hstep := st88_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p141 : ((235264990043/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT88 (i+1))
      = (∑ i ∈ Finset.range 140, stT88 (i+1)) + stT88 141 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 140
    simpa using h
  have hprev := st88_p140
  have hstep := st88_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p142 : ((3345279485961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT88 (i+1))
      = (∑ i ∈ Finset.range 141, stT88 (i+1)) + stT88 142 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 141
    simpa using h
  have hprev := st88_p141
  have hstep := st88_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p143 : ((5982812235059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT88 (i+1))
      = (∑ i ∈ Finset.range 142, stT88 (i+1)) + stT88 143 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 142
    simpa using h
  have hprev := st88_p142
  have hstep := st88_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p144 : ((5661526978031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT88 (i+1))
      = (∑ i ∈ Finset.range 143, stT88 (i+1)) + stT88 144 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 143
    simpa using h
  have hprev := st88_p143
  have hstep := st88_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p145 : ((5837246892161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT88 (i+1))
      = (∑ i ∈ Finset.range 144, stT88 (i+1)) + stT88 145 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 144
    simpa using h
  have hprev := st88_p144
  have hstep := st88_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p146 : ((402575977591/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT88 (i+1))
      = (∑ i ∈ Finset.range 145, stT88 (i+1)) + stT88 146 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 145
    simpa using h
  have hprev := st88_p145
  have hstep := st88_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p147 : ((362822283543/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT88 (i+1))
      = (∑ i ∈ Finset.range 146, stT88 (i+1)) + stT88 147 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 146
    simpa using h
  have hprev := st88_p146
  have hstep := st88_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p148 : ((799849664439/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT88 (i+1))
      = (∑ i ∈ Finset.range 147, stT88 (i+1)) + stT88 148 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 147
    simpa using h
  have hprev := st88_p147
  have hstep := st88_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p149 : ((8415166542531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT88 (i+1))
      = (∑ i ∈ Finset.range 148, stT88 (i+1)) + stT88 149 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 148
    simpa using h
  have hprev := st88_p148
  have hstep := st88_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p150 : ((8370239611603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT88 (i+1))
      = (∑ i ∈ Finset.range 149, stT88 (i+1)) + stT88 150 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 149
    simpa using h
  have hprev := st88_p149
  have hstep := st88_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p151 : ((1576877935049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT88 (i+1))
      = (∑ i ∈ Finset.range 150, stT88 (i+1)) + stT88 151 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 150
    simpa using h
  have hprev := st88_p150
  have hstep := st88_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p152 : ((7122476186553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT88 (i+1))
      = (∑ i ∈ Finset.range 151, stT88 (i+1)) + stT88 152 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 151
    simpa using h
  have hprev := st88_p151
  have hstep := st88_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p153 : ((1583673226101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT88 (i+1))
      = (∑ i ∈ Finset.range 152, stT88 (i+1)) + stT88 153 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 152
    simpa using h
  have hprev := st88_p152
  have hstep := st88_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p154 : ((1443326257483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT88 (i+1))
      = (∑ i ∈ Finset.range 153, stT88 (i+1)) + stT88 154 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 153
    simpa using h
  have hprev := st88_p153
  have hstep := st88_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p155 : ((1403208631363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT88 (i+1))
      = (∑ i ∈ Finset.range 154, stT88 (i+1)) + stT88 155 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 154
    simpa using h
  have hprev := st88_p154
  have hstep := st88_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p156 : ((1474614110083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT88 (i+1))
      = (∑ i ∈ Finset.range 155, stT88 (i+1)) + stT88 156 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 155
    simpa using h
  have hprev := st88_p155
  have hstep := st88_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p157 : ((653680792169/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT88 (i+1))
      = (∑ i ∈ Finset.range 156, stT88 (i+1)) + stT88 157 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 156
    simpa using h
  have hprev := st88_p156
  have hstep := st88_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p158 : ((1832364489103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT88 (i+1))
      = (∑ i ∈ Finset.range 157, stT88 (i+1)) + stT88 158 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 157
    simpa using h
  have hprev := st88_p157
  have hstep := st88_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p159 : ((1607275613291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT88 (i+1))
      = (∑ i ∈ Finset.range 158, stT88 (i+1)) + stT88 159 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 158
    simpa using h
  have hprev := st88_p158
  have hstep := st88_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p160 : ((8448745181407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT88 (i+1))
      = (∑ i ∈ Finset.range 159, stT88 (i+1)) + stT88 160 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 159
    simpa using h
  have hprev := st88_p159
  have hstep := st88_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p161 : ((8449103771457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT88 (i+1))
      = (∑ i ∈ Finset.range 160, stT88 (i+1)) + stT88 161 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 160
    simpa using h
  have hprev := st88_p160
  have hstep := st88_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p162 : ((4021083666791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT88 (i+1))
      = (∑ i ∈ Finset.range 161, stT88 (i+1)) + stT88 162 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 161
    simpa using h
  have hprev := st88_p161
  have hstep := st88_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p163 : ((293965927327/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT88 (i+1))
      = (∑ i ∈ Finset.range 162, stT88 (i+1)) + stT88 163 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 162
    simpa using h
  have hprev := st88_p162
  have hstep := st88_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p164 : ((821168914539/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT88 (i+1))
      = (∑ i ∈ Finset.range 163, stT88 (i+1)) + stT88 164 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 163
    simpa using h
  have hprev := st88_p163
  have hstep := st88_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p165 : ((2960848878619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT88 (i+1))
      = (∑ i ∈ Finset.range 164, stT88 (i+1)) + stT88 165 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 164
    simpa using h
  have hprev := st88_p164
  have hstep := st88_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p166 : ((5583531094991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT88 (i+1))
      = (∑ i ∈ Finset.range 165, stT88 (i+1)) + stT88 166 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 165
    simpa using h
  have hprev := st88_p165
  have hstep := st88_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p167 : ((2821807290913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT88 (i+1))
      = (∑ i ∈ Finset.range 166, stT88 (i+1)) + stT88 167 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 166
    simpa using h
  have hprev := st88_p166
  have hstep := st88_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p168 : ((3040604599417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT88 (i+1))
      = (∑ i ∈ Finset.range 167, stT88 (i+1)) + stT88 168 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 167
    simpa using h
  have hprev := st88_p167
  have hstep := st88_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p169 : ((3387678098497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT88 (i+1))
      = (∑ i ∈ Finset.range 168, stT88 (i+1)) + stT88 169 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 168
    simpa using h
  have hprev := st88_p168
  have hstep := st88_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p170 : ((30160779759/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT88 (i+1))
      = (∑ i ∈ Finset.range 169, stT88 (i+1)) + stT88 170 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 169
    simpa using h
  have hprev := st88_p169
  have hstep := st88_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p171 : ((2043907254043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT88 (i+1))
      = (∑ i ∈ Finset.range 170, stT88 (i+1)) + stT88 171 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 170
    simpa using h
  have hprev := st88_p170
  have hstep := st88_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p172 : ((106492376837/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT88 (i+1))
      = (∑ i ∈ Finset.range 171, stT88 (i+1)) + stT88 172 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 171
    simpa using h
  have hprev := st88_p171
  have hstep := st88_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p173 : ((4243568266991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT88 (i+1))
      = (∑ i ∈ Finset.range 172, stT88 (i+1)) + stT88 173 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 172
    simpa using h
  have hprev := st88_p172
  have hstep := st88_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p174 : ((8091113955471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT88 (i+1))
      = (∑ i ∈ Finset.range 173, stT88 (i+1)) + stT88 174 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 173
    simpa using h
  have hprev := st88_p173
  have hstep := st88_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p175 : ((1858476753771/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT88 (i+1))
      = (∑ i ∈ Finset.range 174, stT88 (i+1)) + stT88 175 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 174
    simpa using h
  have hprev := st88_p174
  have hstep := st88_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p176 : ((3340090389807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT88 (i+1))
      = (∑ i ∈ Finset.range 175, stT88 (i+1)) + stT88 176 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 175
    simpa using h
  have hprev := st88_p175
  have hstep := st88_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p177 : ((1202903386977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT88 (i+1))
      = (∑ i ∈ Finset.range 176, stT88 (i+1)) + stT88 177 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 176
    simpa using h
  have hprev := st88_p176
  have hstep := st88_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p178 : ((5596277329353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT88 (i+1))
      = (∑ i ∈ Finset.range 177, stT88 (i+1)) + stT88 178 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 177
    simpa using h
  have hprev := st88_p177
  have hstep := st88_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p179 : ((5522426915373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT88 (i+1))
      = (∑ i ∈ Finset.range 178, stT88 (i+1)) + stT88 179 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 178
    simpa using h
  have hprev := st88_p178
  have hstep := st88_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p180 : ((1451671296947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT88 (i+1))
      = (∑ i ∈ Finset.range 179, stT88 (i+1)) + stT88 180 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 179
    simpa using h
  have hprev := st88_p179
  have hstep := st88_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p181 : ((3189499262837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT88 (i+1))
      = (∑ i ∈ Finset.range 180, stT88 (i+1)) + stT88 181 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 180
    simpa using h
  have hprev := st88_p180
  have hstep := st88_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p182 : ((1776093604897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT88 (i+1))
      = (∑ i ∈ Finset.range 181, stT88 (i+1)) + stT88 182 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 181
    simpa using h
  have hprev := st88_p181
  have hstep := st88_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p183 : ((7815758574391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT88 (i+1))
      = (∑ i ∈ Finset.range 182, stT88 (i+1)) + stT88 183 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 182
    simpa using h
  have hprev := st88_p182
  have hstep := st88_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p184 : ((4176385180571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT88 (i+1))
      = (∑ i ∈ Finset.range 183, stT88 (i+1)) + stT88 184 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 183
    simpa using h
  have hprev := st88_p183
  have hstep := st88_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p185 : ((2149331699901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT88 (i+1))
      = (∑ i ∈ Finset.range 184, stT88 (i+1)) + stT88 185 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 184
    simpa using h
  have hprev := st88_p184
  have hstep := st88_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p186 : ((531151516359/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT88 (i+1))
      = (∑ i ∈ Finset.range 185, stT88 (i+1)) + stT88 186 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 185
    simpa using h
  have hprev := st88_p185
  have hstep := st88_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p187 : ((8081205958143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT88 (i+1))
      = (∑ i ∈ Finset.range 186, stT88 (i+1)) + stT88 187 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 186
    simpa using h
  have hprev := st88_p186
  have hstep := st88_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p188 : ((3719582922409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT88 (i+1))
      = (∑ i ∈ Finset.range 187, stT88 (i+1)) + stT88 188 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 187
    simpa using h
  have hprev := st88_p187
  have hstep := st88_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p189 : ((1342402431423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT88 (i+1))
      = (∑ i ∈ Finset.range 188, stT88 (i+1)) + stT88 189 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 188
    simpa using h
  have hprev := st88_p188
  have hstep := st88_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p190 : ((6054632781197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT88 (i+1))
      = (∑ i ∈ Finset.range 189, stT88 (i+1)) + stT88 190 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 189
    simpa using h
  have hprev := st88_p189
  have hstep := st88_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p191 : ((700517325509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT88 (i+1))
      = (∑ i ∈ Finset.range 190, stT88 (i+1)) + stT88 191 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 190
    simpa using h
  have hprev := st88_p190
  have hstep := st88_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p192 : ((170372618111/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT88 (i+1))
      = (∑ i ∈ Finset.range 191, stT88 (i+1)) + stT88 192 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 191
    simpa using h
  have hprev := st88_p191
  have hstep := st88_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p193 : ((703282871569/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT88 (i+1))
      = (∑ i ∈ Finset.range 192, stT88 (i+1)) + stT88 193 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 192
    simpa using h
  have hprev := st88_p192
  have hstep := st88_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p194 : ((3044227448337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT88 (i+1))
      = (∑ i ∈ Finset.range 193, stT88 (i+1)) + stT88 194 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 193
    simpa using h
  have hprev := st88_p193
  have hstep := st88_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p195 : ((3371309653381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT88 (i+1))
      = (∑ i ∈ Finset.range 194, stT88 (i+1)) + stT88 195 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 194
    simpa using h
  have hprev := st88_p194
  have hstep := st88_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p196 : ((932065002679/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT88 (i+1))
      = (∑ i ∈ Finset.range 195, stT88 (i+1)) + stT88 196 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 195
    simpa using h
  have hprev := st88_p195
  have hstep := st88_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p197 : ((2022186131333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT88 (i+1))
      = (∑ i ∈ Finset.range 196, stT88 (i+1)) + stT88 197 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 196
    simpa using h
  have hprev := st88_p196
  have hstep := st88_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p198 : ((2129153186537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT88 (i+1))
      = (∑ i ∈ Finset.range 197, stT88 (i+1)) + stT88 198 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 197
    simpa using h
  have hprev := st88_p197
  have hstep := st88_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p199 : ((8659369328571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT88 (i+1))
      = (∑ i ∈ Finset.range 198, stT88 (i+1)) + stT88 199 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 198
    simpa using h
  have hprev := st88_p198
  have hstep := st88_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_p200 : ((8492432679583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT88 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT88 (i+1))
      = (∑ i ∈ Finset.range 199, stT88 (i+1)) + stT88 200 := by
    have h := Finset.sum_range_succ (fun i => stT88 (i+1)) 199
    simpa using h
  have hprev := st88_p199
  have hstep := st88_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st88_s200 :
    |Real.sin (((88 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-16027/31250 : ℚ) : ℝ))
      - ((194349/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 2261349/5000000) (δ := 111/20000000) (ψ := -16027/31250) 88 74
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 88`** (evaluated boundary). -/
theorem station_88_sign : hardyG (((88:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower_eval 88 200 (by norm_num) (by norm_num)
    ((-16027/31250 : ℚ) : ℝ)
  have hchain := st88_p200
  have hbridge : (∑ i ∈ Finset.range 200, stT88 (i+1))
      = ∑ i ∈ Finset.range 200,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((88:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-16027/31250 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_200
  have hsh := rpow_half_shifts (N := 200) (by norm_num)
  have hcosb := abs_le.mp st88_c200
  have hsinb := abs_le.mp st88_s200
  have hbdy_lo : ((-1887091099143/12100390625000 : ℚ) : ℝ)
      ≤ ((200:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos ((((88:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((-16027/31250 : ℚ) : ℝ))) / 2
          - (((88:ℕ)):ℝ)
            * Real.sin ((((88:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((-16027/31250 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + (((88:ℕ)):ℝ) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((88:ℝ) * Real.log (200:ℝ) - ((-16027/31250 : ℚ) : ℝ))) / 2
        - (88:ℝ) * Real.sin ((88:ℝ) * Real.log (200:ℝ) - ((-16027/31250 : ℚ) : ℝ))
        ≥ ((-2668749/31250 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hEneg : -(Real.cos ((88:ℝ) * Real.log (200:ℝ) - ((-16027/31250 : ℚ) : ℝ))) / 2
        - (88:ℝ) * Real.sin ((88:ℝ) * Real.log (200:ℝ) - ((-16027/31250 : ℚ) : ℝ))
        ≤ 0 := by
      nlinarith [hcosb.1, hsinb.1,
        Real.neg_one_le_cos ((88:ℝ) * Real.log (200:ℝ) - ((-16027/31250 : ℚ) : ℝ)),
        Real.neg_one_le_sin ((88:ℝ) * Real.log (200:ℝ) - ((-16027/31250 : ℚ) : ℝ))]
    have hsqpos : (0:ℝ) ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (200:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + (88:ℝ) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-2668749/31250 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (200:ℝ) * (707107/10000000)
          * ((-2668749/31250 : ℚ) : ℝ)
        ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ)))
          * ((-2668749/31250 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((200:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((88:ℕ)):ℝ)+1) * ((((88:ℕ)):ℝ)+2) / 8
        * (((200:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((200:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((87399132307/320000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8492432679583/10000000000000 : ℚ) : ℝ) + ((-1887091099143/12100390625000 : ℚ) : ℝ)
      - ((87399132307/320000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-16027/31250 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((88:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-16027/31250 : ℚ) : ℝ)
        * (riemannZeta (line (((88:ℕ)):ℝ))).re
      - Real.sin ((-16027/31250 : ℚ) : ℝ)
        * (riemannZeta (line (((88:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((88:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((88:ℕ)):ℝ)
      = ((((88:ℕ)):ℝ) * (Real.log (((88:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((88:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_88
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
  have hθwin : |(((-16027/31250 : ℚ) : ℝ) + ((12:ℤ)) * (2*Real.pi) - Real.pi)
      - theta (((88:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((88:ℕ)):ℝ))
    (φ := ((-16027/31250 : ℚ) : ℝ) + ((12:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-16027/31250 : ℚ) : ℝ) + ((12:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-16027/31250 : ℚ)) : ℝ) - Real.pi) + ((12:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-16027/31250 : ℚ)) : ℝ) - Real.pi) 12).1,
    (cos_sin_shift ((((-16027/31250 : ℚ)) : ℝ) - Real.pi) 12).2]
  exact cos_sin_flip ((-16027/31250 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_88_sign
end AxiomAudit
