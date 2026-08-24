import RequestProject.DVPSqrtTable

/-!
# Station `t = 42` of the Hardy ladder (sign +)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT42 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((42 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-69223/200000 : ℚ) : ℝ))

theorem st42_c1 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((470349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108161/1250000) (δ := 21/100000000) (ψ := -69223/200000) 42 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t1 : ((117581/125000 : ℚ) : ℝ) ≤ stT42 1 := by
  have hc : ((117581/125000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117581/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((117581/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c2 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-188629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195763/400000) (δ := 67/20000000) (ψ := -69223/200000) 42 5
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t2 : ((-166748157809/625000000000 : ℚ) : ℝ) ≤ stT42 2 := by
  have hc : ((-94327/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166748157809/625000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-94327/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c3 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-804443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252767/2000000) (δ := 377/100000000) (ψ := -69223/200000) 42 7
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t3 : ((-4644742748979/10000000000000 : ℚ) : ℝ) ≤ stT42 3 := by
  have hc : ((-804493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4644742748979/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-804493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c4 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-217939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2527263/5000000) (δ := 129/50000000) (ψ := -69223/200000) 42 9
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t4 : ((-272455054491/1250000000000 : ℚ) : ℝ) ≤ stT42 4 := by
  have hc : ((-54491/125000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272455054491/1250000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-54491/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c5 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((19391/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22901/78125) (δ := 3/781250) (ψ := -69223/200000) 42 11
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t5 : ((34683195779/200000000000 : ℚ) : ℝ) ≤ stT42 5 := by
  have hc : ((38777/100000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34683195779/200000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((38777/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c6 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((97971/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504473/10000000) (δ := 31/10000000) (ψ := -69223/200000) 42 12
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t6 : ((99986107903/250000000000 : ℚ) : ℝ) ≤ stT42 6 := by
  have hc : ((48983/50000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99986107903/250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((48983/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c7 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((92379/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 982331/10000000) (δ := 221/100000000) (ψ := -69223/200000) 42 13
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t7 : ((43642604357/125000000000 : ℚ) : ℝ) ≤ stT42 7 := by
  have hc : ((46187/50000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43642604357/125000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((46187/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c8 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((960519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176209/2500000) (δ := 231/100000000) (ψ := -69223/200000) 42 14
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t8 : ((3395769844977/10000000000000 : ℚ) : ℝ) ≤ stT42 8 := by
  have hc : ((960469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3395769844977/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((960469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c9 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-23709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4045581/10000000) (δ := 161/50000000) (ψ := -69223/200000) 42 15
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t9 : ((-19778337289/1250000000000 : ℚ) : ℝ) ≤ stT42 9 := by
  have hc : ((-11867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19778337289/1250000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-11867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c10 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-472257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7017273/10000000) (δ := 191/50000000) (ψ := -69223/200000) 42 15
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t10 : ((-373371744599/1250000000000 : ℚ) : ℝ) ≤ stT42 10 := by
  have hc : ((-236141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373371744599/1250000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-236141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c11 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((172889/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1316879/10000000) (δ := 313/100000000) (ψ := -69223/200000) 42 16
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t11 : ((521249720327/2000000000000 : ℚ) : ℝ) ≤ stT42 11 := by
  have hc : ((172879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((521249720327/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((172879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c12 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-253267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525489/1000000) (δ := 219/100000000) (ψ := -69223/200000) 42 17
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t12 : ((-5712431153/39062500000 : ℚ) : ℝ) ≤ stT42 12 := by
  have hc : ((-63323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5712431153/39062500000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-63323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c13 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((76493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1574797/5000000) (δ := 7/3125000) (ψ := -69223/200000) 42 17
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t13 : ((848474667/10000000000 : ℚ) : ℝ) ≤ stT42 13 := by
  have hc : ((152961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((848474667/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((152961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c14 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-333503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -597129/1250000) (δ := 309/100000000) (ψ := -69223/200000) 42 18
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t14 : ((-891458083989/10000000000000 : ℚ) : ℝ) ≤ stT42 14 := by
  have hc : ((-333553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-891458083989/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-333553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c15 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((551289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123361/500000) (δ := 409/100000000) (ψ := -69223/200000) 42 18
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t15 : ((355823120783/2500000000000 : ℚ) : ℝ) ≤ stT42 15 := by
  have hc : ((551239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355823120783/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((551239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c16 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-849419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6464199/10000000) (δ := 169/50000000) (ψ := -69223/200000) 42 19
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t16 : ((-2123673349469/10000000000000 : ℚ) : ℝ) ≤ stT42 16 := by
  have hc : ((-849469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2123673349469/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-849469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c17 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((499611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98613/10000000) (δ := 109/50000000) (ψ := -69223/200000) 42 19
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t17 : ((151459237827/625000000000 : ℚ) : ℝ) ≤ stT42 17 := by
  have hc : ((249793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151459237827/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((249793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c18 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-710643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295151/500000) (δ := 49/20000000) (ψ := -69223/200000) 42 19
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t18 : ((-1675119746939/10000000000000 : ℚ) : ℝ) ≤ stT42 18 := by
  have hc : ((-710693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1675119746939/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-710693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c19 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-80271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -825577/2000000) (δ := 21/6250000) (ψ := -69223/200000) 42 20
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t19 : ((-92134532359/5000000000000 : ℚ) : ℝ) ≤ stT42 19 := by
  have hc : ((-80321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92134532359/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-80321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c20 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((876061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1257911/10000000) (δ := 79/25000000) (ψ := -69223/200000) 42 20
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t20 : ((1958819288737/10000000000000 : ℚ) : ℝ) ≤ stT42 20 := by
  have hc : ((876011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1958819288737/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((876011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c21 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-415681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3190439/5000000) (δ := 267/100000000) (ψ := -69223/200000) 42 20
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t21 : ((-453572451687/2500000000000 : ℚ) : ℝ) ≤ stT42 21 := by
  have hc : ((-207853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453572451687/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-207853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c22 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-204739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1110621/2500000) (δ := 27/12500000) (ψ := -69223/200000) 42 21
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t22 : ((-54576473289/1250000000000 : ℚ) : ℝ) ≤ stT42 22 := by
  have hc : ((-204789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54576473289/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-204789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c23 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((497977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28119/1250000) (δ := 21/6250000) (ψ := -69223/200000) 42 21
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t23 : ((4055865723/19531250000 : ℚ) : ℝ) ≤ stT42 23 := by
  have hc : ((15561/15625 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4055865723/19531250000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((15561/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c24 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-301903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4693711/10000000) (δ := 37/12500000) (ψ := -69223/200000) 42 21
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t24 : ((-308179572813/5000000000000 : ℚ) : ℝ) ≤ stT42 24 := by
  have hc : ((-301953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308179572813/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-301953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c25 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-450133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6727943/10000000) (δ := 163/50000000) (ψ := -69223/200000) 42 22
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t25 : ((-450158225079/2500000000000 : ℚ) : ℝ) ≤ stT42 25 := by
  have hc : ((-225079/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450158225079/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-225079/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c26 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((502847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326221/1250000) (δ := 133/50000000) (ψ := -69223/200000) 42 22
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t26 : ((986065867317/10000000000000 : ℚ) : ℝ) ≤ stT42 26 := by
  have hc : ((502797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986065867317/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((502797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c27 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((428549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1352967/10000000) (δ := 297/100000000) (ψ := -69223/200000) 42 22
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t27 : ((412347219/2500000000 : ℚ) : ℝ) ≤ stT42 27 := by
  have hc : ((107131/125000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((412347219/2500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((107131/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c28 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-477521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5171569/10000000) (δ := 193/50000000) (ψ := -69223/200000) 42 22
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t28 : ((-902524659933/10000000000000 : ℚ) : ℝ) ≤ stT42 28 := by
  have hc : ((-477571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-902524659933/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-477571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c29 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-460361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3425903/5000000) (δ := 63/20000000) (ψ := -69223/200000) 42 23
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t29 : ((-213728906061/1250000000000 : ℚ) : ℝ) ≤ stT42 29 := by
  have hc : ((-230193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213728906061/1250000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-230193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c30 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((251219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3292143/10000000) (δ := 41/12500000) (ψ := -69223/200000) 42 23
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t30 : ((458569541229/10000000000000 : ℚ) : ℝ) ≤ stT42 30 := by
  have hc : ((251169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458569541229/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((251169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c31 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((499091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150789/10000000) (δ := 79/20000000) (ψ := -69223/200000) 42 23
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t31 : ((448174493249/2500000000000 : ℚ) : ℝ) ≤ stT42 31 := by
  have hc : ((249533/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448174493249/2500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((249533/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c32 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((11007/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1742201/5000000) (δ := 83/20000000) (ψ := -69223/200000) 42 23
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t32 : ((77809104373/2500000000000 : ℚ) : ℝ) ≤ stT42 32 := by
  have hc : ((88031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77809104373/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((88031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c33 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-35923/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3357713/5000000) (δ := 31/12500000) (ψ := -69223/200000) 42 23
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t33 : ((-2501496549/16000000000 : ℚ) : ℝ) ≤ stT42 33 := by
  have hc : ((-1437/1600 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2501496549/16000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-1437/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c34 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-174463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -732247/1250000) (δ := 81/25000000) (ψ := -69223/200000) 42 24
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t34 : ((-299223039843/2500000000000 : ℚ) : ℝ) ≤ stT42 34 := by
  have hc : ((-348951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299223039843/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-348951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c35 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((430533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703571/2500000) (δ := 279/100000000) (ψ := -69223/200000) 42 24
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t35 : ((181912214691/2500000000000 : ℚ) : ℝ) ≤ stT42 35 := by
  have hc : ((430483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181912214691/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((430483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c36 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((998349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71829/5000000) (δ := 61/25000000) (ψ := -69223/200000) 42 24
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t36 : ((831915500567/5000000000000 : ℚ) : ℝ) ≤ stT42 36 := by
  have hc : ((998299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((831915500567/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((998299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c37 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((88671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60411/200000) (δ := 91/25000000) (ψ := -69223/200000) 42 24
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t37 : ((291507197513/5000000000000 : ℚ) : ℝ) ≤ stT42 37 := by
  have hc : ((177317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291507197513/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((177317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c38 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-6871/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1455179/2500000) (δ := 259/100000000) (ψ := -69223/200000) 42 24
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t38 : ((-4458820149/40000000000 : ℚ) : ℝ) ≤ stT42 38 := by
  have hc : ((-13743/20000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4458820149/40000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-13743/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c39 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-480849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7159821/10000000) (δ := 107/50000000) (ψ := -69223/200000) 42 25
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t39 : ((-192503720117/1250000000000 : ℚ) : ℝ) ≤ stT42 39 := by
  have hc : ((-240437/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192503720117/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-240437/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c40 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-28471/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1125363/2500000) (δ := 107/50000000) (ψ := -69223/200000) 42 25
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t40 : ((-180105962351/5000000000000 : ℚ) : ℝ) ≤ stT42 40 := by
  have hc : ((-113909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180105962351/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-113909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c41 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((722427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1908727/10000000) (δ := 289/100000000) (ψ := -69223/200000) 42 25
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t41 : ((1128162888849/10000000000000 : ℚ) : ℝ) ≤ stT42 41 := by
  have hc : ((722377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1128162888849/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((722377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c42 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((121157/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155379/2500000) (δ := 167/50000000) (ψ := -69223/200000) 42 25
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t42 : ((747758420899/5000000000000 : ℚ) : ℝ) ≤ stT42 42 := by
  have hc : ((484603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((747758420899/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((484603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c43 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((327739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1546109/5000000) (δ := 177/50000000) (ψ := -69223/200000) 42 25
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t43 : ((99944161933/2000000000000 : ℚ) : ℝ) ≤ stT42 43 := by
  have hc : ((327689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99944161933/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((327689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c44 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-295239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5506117/10000000) (δ := 147/50000000) (ψ := -69223/200000) 42 25
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t44 : ((-13910228439/156250000000 : ℚ) : ℝ) ≤ stT42 44 := by
  have hc : ((-9227/15625 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13910228439/156250000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-9227/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c45 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-999989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1960549/2500000) (δ := 19/5000000) (ψ := -69223/200000) 42 26
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t45 : ((-186346267221/1250000000000 : ℚ) : ℝ) ≤ stT42 45 := by
  have hc : ((-1000039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186346267221/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-1000039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c46 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-599573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5534411/10000000) (δ := 1/250000) (ψ := -69223/200000) 42 26
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t46 : ((-44204807183/500000000000 : ℚ) : ℝ) ≤ stT42 46 := by
  have hc : ((-599623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44204807183/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-599623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c47 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((257363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3276259/10000000) (δ := 403/100000000) (ψ := -69223/200000) 42 26
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t47 : ((375329350137/10000000000000 : ℚ) : ℝ) ≤ stT42 47 := by
  have hc : ((257313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375329350137/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((257313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c48 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((455259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1065651/10000000) (δ := 363/100000000) (ψ := -69223/200000) 42 26
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t48 : ((2628293499/20000000000 : ℚ) : ℝ) ≤ stT42 48 := by
  have hc : ((227617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2628293499/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((227617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c49 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((452429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 549687/5000000) (δ := 21/5000000) (ψ := -69223/200000) 42 26
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t49 : ((161572808671/1250000000000 : ℚ) : ℝ) ≤ stT42 49 := by
  have hc : ((113101/125000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161572808671/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((113101/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c50 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((278789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1610329/5000000) (δ := 403/100000000) (ψ := -69223/200000) 42 26
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t50 : ((394196317407/10000000000000 : ℚ) : ℝ) ≤ stT42 50 := by
  have hc : ((278739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394196317407/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((278739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c51 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-260993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2649967/5000000) (δ := 283/100000000) (ψ := -69223/200000) 42 26
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t51 : ((-182749273029/2500000000000 : ℚ) : ℝ) ≤ stT42 51 := by
  have hc : ((-130509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182749273029/2500000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-130509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c52 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-195769/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7338833/10000000) (δ := 343/100000000) (ψ := -69223/200000) 42 26
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t52 : ((-271496724029/2000000000000 : ℚ) : ℝ) ≤ stT42 52 := by
  have hc : ((-195779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271496724029/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-195779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c53 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-103591/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636907/1000000) (δ := 93/25000000) (ψ := -69223/200000) 42 27
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t53 : ((-284603608367/2500000000000 : ℚ) : ℝ) ≤ stT42 53 := by
  have hc : ((-414389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284603608367/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-414389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c54 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-190589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1101599/2500000) (δ := 29/12500000) (ψ := -69223/200000) 42 27
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t54 : ((-64856722273/2500000000000 : ℚ) : ℝ) ≤ stT42 54 := by
  have hc : ((-190639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64856722273/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-190639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c55 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((109421/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -309967/1250000) (δ := 371/100000000) (ψ := -69223/200000) 42 27
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t55 : ((147529682989/2000000000000 : ℚ) : ℝ) ≤ stT42 55 := by
  have hc : ((109411/200000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147529682989/2000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((109411/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c56 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((972487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -587793/10000000) (δ := 391/100000000) (ψ := -69223/200000) 42 27
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t56 : ((649736698861/5000000000000 : ℚ) : ℝ) ≤ stT42 56 := by
  have hc : ((972437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((649736698861/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((972437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c57 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((87359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 635331/5000000) (δ := 271/100000000) (ψ := -69223/200000) 42 27
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t57 : ((14462896041/125000000000 : ℚ) : ℝ) ≤ stT42 57 := by
  have hc : ((43677/50000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14462896041/125000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((43677/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c58 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((326009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 619359/2000000) (δ := 49/12500000) (ψ := -69223/200000) 42 27
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t58 : ((53500628547/1250000000000 : ℚ) : ℝ) ≤ stT42 58 := by
  have hc : ((325959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53500628547/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((325959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c59 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-188191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4891711/10000000) (δ := 29/12500000) (ψ := -69223/200000) 42 27
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t59 : ((-3062956603/62500000000 : ℚ) : ℝ) ≤ stT42 59 := by
  have hc : ((-23527/62500 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3062956603/62500000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-23527/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c60 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-221863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3328229/5000000) (δ := 251/100000000) (ψ := -69223/200000) 42 27
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t60 : ((-114576064449/1000000000000 : ℚ) : ℝ) ≤ stT42 60 := by
  have hc : ((-443751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114576064449/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-443751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c61 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-976929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914491/1250000) (δ := 141/50000000) (ψ := -69223/200000) 42 28
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t61 : ((-1250893625251/10000000000000 : ℚ) : ℝ) ≤ stT42 61 := by
  have hc : ((-976979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1250893625251/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-976979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c62 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-77881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2804287/5000000) (δ := 171/50000000) (ψ := -69223/200000) 42 28
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t62 : ((-197833926549/2500000000000 : ℚ) : ℝ) ≤ stT42 62 := by
  have hc : ((-311549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197833926549/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-311549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c63 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1964269/5000000) (δ := 321/100000000) (ψ := -69223/200000) 42 28
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t63 : ((-421430529/5000000000000 : ℚ) : ℝ) ≤ stT42 63 := by
  have hc : ((-669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421430529/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c64 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((306879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28437/125000) (δ := 181/50000000) (ψ := -69223/200000) 42 28
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t64 : ((153427/2000000 : ℚ) : ℝ) ≤ stT42 64 := by
  have hc : ((153427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153427/2000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((153427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c65 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((120837/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647021/10000000) (δ := 141/50000000) (ψ := -69223/200000) 42 28
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t65 : ((599488233081/5000000000000 : ℚ) : ℝ) ≤ stT42 65 := by
  have hc : ((483323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((599488233081/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((483323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c66 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((463881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29877/312500) (δ := 241/100000000) (ψ := -69223/200000) 42 28
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t66 : ((17842713887/156250000000 : ℚ) : ℝ) ≤ stT42 66 := by
  have hc : ((28991/31250 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17842713887/156250000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((28991/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c67 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((105691/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2535041/10000000) (δ := 341/100000000) (ψ := -69223/200000) 42 28
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t67 : ((64554921807/1000000000000 : ℚ) : ℝ) ≤ stT42 67 := by
  have hc : ((105681/200000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64554921807/1000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((105681/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c68 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-65407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1309/3200) (δ := 401/100000000) (ψ := -69223/200000) 42 28
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t68 : ((-79378329303/10000000000000 : ℚ) : ℝ) ≤ stT42 68 := by
  have hc : ((-65457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79378329303/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-65457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c69 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-313853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5623499/10000000) (δ := 401/100000000) (ψ := -69223/200000) 42 28
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t69 : ((-188932427601/2500000000000 : ℚ) : ℝ) ≤ stT42 69 := by
  have hc : ((-156939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188932427601/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-156939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c70 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-239713/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1783579/2500000) (δ := 261/100000000) (ψ := -69223/200000) 42 28
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t70 : ((-573053739279/5000000000000 : ℚ) : ℝ) ≤ stT42 70 := by
  have hc : ((-479451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573053739279/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-479451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c71 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-59561/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -354213/500000) (δ := 83/25000000) (ψ := -69223/200000) 42 29
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t71 : ((-282758525583/2500000000000 : ℚ) : ℝ) ≤ stT42 71 := by
  have hc : ((-476513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282758525583/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-476513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c72 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-156319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1123141/2000000) (δ := 351/100000000) (ψ := -69223/200000) 42 29
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t72 : ((-23029818591/312500000000 : ℚ) : ℝ) ≤ stT42 72 := by
  have hc : ((-312663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23029818591/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-312663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c73 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-48009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2083703/5000000) (δ := 251/100000000) (ψ := -69223/200000) 42 29
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t73 : ((-7027446251/625000000000 : ℚ) : ℝ) ≤ stT42 73 := by
  have hc : ((-24017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7027446251/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-24017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c74 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((22879/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -684703/2500000) (δ := 103/25000000) (ψ := -69223/200000) 42 29
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t74 : ((13296691107/250000000000 : ℚ) : ℝ) ≤ stT42 74 := by
  have hc : ((45753/100000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13296691107/250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((45753/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c75 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((861917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -265879/2000000) (δ := 351/100000000) (ψ := -69223/200000) 42 29
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t75 : ((9951978249/100000000000 : ℚ) : ℝ) ≤ stT42 75 := by
  have hc : ((861867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9951978249/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((861867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c76 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((999699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61353/10000000) (δ := 271/100000000) (ψ := -69223/200000) 42 29
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t76 : ((573337687811/5000000000000 : ℚ) : ℝ) ≤ stT42 76 := by
  have hc : ((999649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((573337687811/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((999649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c77 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((83997/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 716961/5000000) (δ := 331/100000000) (ψ := -69223/200000) 42 29
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t77 : ((2392942579/25000000000 : ℚ) : ℝ) ≤ stT42 77 := by
  have hc : ((10499/12500 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2392942579/25000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((10499/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c78 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((219859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139439/500000) (δ := 291/100000000) (ψ := -69223/200000) 42 29
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t78 : ((124456491009/2500000000000 : ℚ) : ℝ) ≤ stT42 78 := by
  have hc : ((109917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124456491009/2500000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((109917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c79 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-7967/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4126377/10000000) (δ := 53/25000000) (ψ := -69223/200000) 42 29
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t79 : ((-70071887/7812500000 : ℚ) : ℝ) ≤ stT42 79 := by
  have hc : ((-1993/25000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70071887/7812500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-1993/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c80 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-571279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5447149/10000000) (δ := 291/100000000) (ψ := -69223/200000) 42 29
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t80 : ((-319382623593/5000000000000 : ℚ) : ℝ) ≤ stT42 80 := by
  have hc : ((-571329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319382623593/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-571329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c81 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-904331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3375757/5000000) (δ := 29/12500000) (ψ := -69223/200000) 42 29
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t81 : ((-125608572709/1250000000000 : ℚ) : ℝ) ≤ stT42 81 := by
  have hc : ((-904381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125608572709/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-904381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c82 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-997237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766809/1000000) (δ := 3/1250000) (ψ := -69223/200000) 42 30
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t82 : ((-275329997673/2500000000000 : ℚ) : ℝ) ≤ stT42 82 := by
  have hc : ((-997287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275329997673/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-997287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c83 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-166913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6395347/10000000) (δ := 1/250000) (ψ := -69223/200000) 42 30
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t83 : ((-183221862489/2000000000000 : ℚ) : ℝ) ≤ stT42 83 := by
  have hc : ((-166923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183221862489/2000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-166923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c84 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-465627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5137847/10000000) (δ := 11/2500000) (ψ := -69223/200000) 42 30
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t84 : ((-50809551793/1000000000000 : ℚ) : ℝ) ≤ stT42 84 := by
  have hc : ((-465677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50809551793/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-465677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c85 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((397/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3895229/10000000) (δ := 223/100000000) (ψ := -69223/200000) 42 30
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t85 : ((1715648301/1250000000000 : ℚ) : ℝ) ≤ stT42 85 := by
  have hc : ((6327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1715648301/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((6327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c86 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((241439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -333393/1250000) (δ := 423/100000000) (ψ := -69223/200000) 42 30
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t86 : ((130161617189/2500000000000 : ℚ) : ℝ) ≤ stT42 86 := by
  have hc : ((120707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130161617189/2500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((120707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c87 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((208937/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726629/5000000) (δ := 17/5000000) (ψ := -69223/200000) 42 30
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t87 : ((27998807943/312500000000 : ℚ) : ℝ) ≤ stT42 87 := by
  have hc : ((417849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27998807943/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((417849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c88 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((497437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50649/2000000) (δ := 9/2500000) (ψ := -69223/200000) 42 30
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t88 : ((132560671059/1250000000000 : ℚ) : ℝ) ≤ stT42 88 := by
  have hc : ((124353/125000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132560671059/1250000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((124353/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c89 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((186227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116651/1250000) (δ := 283/100000000) (ψ := -69223/200000) 42 30
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t89 : ((197389461349/2000000000000 : ℚ) : ℝ) ≤ stT42 89 := by
  have hc : ((186217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197389461349/2000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((186217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c90 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((665553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 421281/2000000) (δ := 303/100000000) (ψ := -69223/200000) 42 30
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t90 : ((175375347069/2500000000000 : ℚ) : ℝ) ≤ stT42 90 := by
  have hc : ((665503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175375347069/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((665503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c91 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((6527/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1633319/5000000) (δ := 463/100000000) (ψ := -69223/200000) 42 30
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t91 : ((6840839313/250000000000 : ℚ) : ℝ) ≤ stT42 91 := by
  have hc : ((26103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6840839313/250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((26103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c92 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-12103/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441419/1000000) (δ := 323/100000000) (ψ := -69223/200000) 42 30
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t92 : ((-100972152477/5000000000000 : ℚ) : ℝ) ≤ stT42 92 := by
  have hc : ((-96849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100972152477/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-96849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c93 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-604341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693667/1250000) (δ := 383/100000000) (ψ := -69223/200000) 42 30
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t93 : ((-78340557029/1250000000000 : ℚ) : ℝ) ≤ stT42 93 := by
  have hc : ((-604391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78340557029/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-604391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c94 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-445181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3336171/5000000) (δ := 363/100000000) (ψ := -69223/200000) 42 30
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t94 : ((-114798815733/1250000000000 : ℚ) : ℝ) ≤ stT42 94 := by
  have hc : ((-222603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114798815733/1250000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-222603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c95 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-499801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7783463/10000000) (δ := 383/100000000) (ψ := -69223/200000) 42 30
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t95 : ((-256405489827/2500000000000 : ℚ) : ℝ) ≤ stT42 95 := by
  have hc : ((-249913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256405489827/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-249913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c96 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-916487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3412507/5000000) (δ := 187/50000000) (ψ := -69223/200000) 42 31
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t96 : ((-935436909477/10000000000000 : ℚ) : ℝ) ≤ stT42 96 := by
  have hc : ((-916537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-935436909477/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-916537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c97 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-331183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5736921/10000000) (δ := 167/50000000) (ψ := -69223/200000) 42 31
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t97 : ((-42036381147/625000000000 : ℚ) : ℝ) ≤ stT42 97 := by
  have hc : ((-41401/62500 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42036381147/625000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-41401/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c98 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((-36127/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4659989/10000000) (δ := 157/50000000) (ψ := -69223/200000) 42 31
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t98 : ((-146000443549/5000000000000 : ℚ) : ℝ) ≤ stT42 98 := by
  have hc : ((-144533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146000443549/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-144533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c99 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((132807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359399/1000000) (δ := 229/100000000) (ψ := -69223/200000) 42 31
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t99 : ((133425697009/10000000000000 : ℚ) : ℝ) ≤ stT42 99 := by
  have hc : ((132757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133425697009/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((132757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_c100 :
    |Real.cos (((42 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-69223/200000 : ℚ) : ℝ))
      - ((527211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158669/625000) (δ := 187/50000000) (ψ := -69223/200000) 42 31
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st42_t100 : ((527160472839/10000000000000 : ℚ) : ℝ) ≤ stT42 100 := by
  have hc : ((527161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((42 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-69223/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st42_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527160472839/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((527161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st42_p1 : ((117581/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT42 (i+1) := by
  rw [Finset.sum_range_one]
  exact st42_t1

theorem st42_p2 : ((421156842191/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT42 (i+1))
      = (∑ i ∈ Finset.range 1, stT42 (i+1)) + stT42 2 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 1
    simpa using h
  have hprev := st42_p1
  have hstep := st42_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p3 : ((2093766726077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT42 (i+1))
      = (∑ i ∈ Finset.range 2, stT42 (i+1)) + stT42 3 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 2
    simpa using h
  have hprev := st42_p2
  have hstep := st42_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p4 : ((-85873709851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT42 (i+1))
      = (∑ i ∈ Finset.range 3, stT42 (i+1)) + stT42 4 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 3
    simpa using h
  have hprev := st42_p3
  have hstep := st42_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p5 : ((1648286079099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT42 (i+1))
      = (∑ i ∈ Finset.range 4, stT42 (i+1)) + stT42 5 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 4
    simpa using h
  have hprev := st42_p4
  have hstep := st42_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p6 : ((5647730395219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT42 (i+1))
      = (∑ i ∈ Finset.range 5, stT42 (i+1)) + stT42 6 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 5
    simpa using h
  have hprev := st42_p5
  have hstep := st42_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p7 : ((9139138743779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT42 (i+1))
      = (∑ i ∈ Finset.range 6, stT42 (i+1)) + stT42 7 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 6
    simpa using h
  have hprev := st42_p6
  have hstep := st42_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p8 : ((3133727147189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT42 (i+1))
      = (∑ i ∈ Finset.range 7, stT42 (i+1)) + stT42 8 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 7
    simpa using h
  have hprev := st42_p7
  have hstep := st42_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p9 : ((3094170472611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT42 (i+1))
      = (∑ i ∈ Finset.range 8, stT42 (i+1)) + stT42 9 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 8
    simpa using h
  have hprev := st42_p8
  have hstep := st42_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p10 : ((2347426983413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT42 (i+1))
      = (∑ i ∈ Finset.range 9, stT42 (i+1)) + stT42 10 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 9
    simpa using h
  have hprev := st42_p9
  have hstep := st42_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p11 : ((11995956535287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT42 (i+1))
      = (∑ i ∈ Finset.range 10, stT42 (i+1)) + stT42 11 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 10
    simpa using h
  have hprev := st42_p10
  have hstep := st42_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p12 : ((10533574160119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT42 (i+1))
      = (∑ i ∈ Finset.range 11, stT42 (i+1)) + stT42 12 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 11
    simpa using h
  have hprev := st42_p11
  have hstep := st42_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p13 : ((11382048827119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT42 (i+1))
      = (∑ i ∈ Finset.range 12, stT42 (i+1)) + stT42 13 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 12
    simpa using h
  have hprev := st42_p12
  have hstep := st42_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p14 : ((1049059074313/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT42 (i+1))
      = (∑ i ∈ Finset.range 13, stT42 (i+1)) + stT42 14 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 13
    simpa using h
  have hprev := st42_p13
  have hstep := st42_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p15 : ((5956941613131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT42 (i+1))
      = (∑ i ∈ Finset.range 14, stT42 (i+1)) + stT42 15 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 14
    simpa using h
  have hprev := st42_p14
  have hstep := st42_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p16 : ((9790209876793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT42 (i+1))
      = (∑ i ∈ Finset.range 15, stT42 (i+1)) + stT42 16 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 15
    simpa using h
  have hprev := st42_p15
  have hstep := st42_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p17 : ((488542307281/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT42 (i+1))
      = (∑ i ∈ Finset.range 16, stT42 (i+1)) + stT42 17 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 16
    simpa using h
  have hprev := st42_p16
  have hstep := st42_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p18 : ((5269218967543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT42 (i+1))
      = (∑ i ∈ Finset.range 17, stT42 (i+1)) + stT42 18 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 17
    simpa using h
  have hprev := st42_p17
  have hstep := st42_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p19 : ((323567777199/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT42 (i+1))
      = (∑ i ∈ Finset.range 18, stT42 (i+1)) + stT42 19 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 18
    simpa using h
  have hprev := st42_p18
  have hstep := st42_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p20 : ((2462597631821/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT42 (i+1))
      = (∑ i ∈ Finset.range 19, stT42 (i+1)) + stT42 20 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 19
    simpa using h
  have hprev := st42_p19
  have hstep := st42_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p21 : ((10498698352357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT42 (i+1))
      = (∑ i ∈ Finset.range 20, stT42 (i+1)) + stT42 21 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 20
    simpa using h
  have hprev := st42_p20
  have hstep := st42_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p22 : ((2012417313209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT42 (i+1))
      = (∑ i ∈ Finset.range 21, stT42 (i+1)) + stT42 22 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 21
    simpa using h
  have hprev := st42_p21
  have hstep := st42_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p23 : ((12138689816221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT42 (i+1))
      = (∑ i ∈ Finset.range 22, stT42 (i+1)) + stT42 23 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 22
    simpa using h
  have hprev := st42_p22
  have hstep := st42_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p24 : ((2304466134119/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT42 (i+1))
      = (∑ i ∈ Finset.range 23, stT42 (i+1)) + stT42 24 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 23
    simpa using h
  have hprev := st42_p23
  have hstep := st42_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p25 : ((9721697770279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT42 (i+1))
      = (∑ i ∈ Finset.range 24, stT42 (i+1)) + stT42 25 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 24
    simpa using h
  have hprev := st42_p24
  have hstep := st42_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p26 : ((2676940909399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT42 (i+1))
      = (∑ i ∈ Finset.range 25, stT42 (i+1)) + stT42 26 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 25
    simpa using h
  have hprev := st42_p25
  have hstep := st42_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p27 : ((3089288128399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT42 (i+1))
      = (∑ i ∈ Finset.range 26, stT42 (i+1)) + stT42 27 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 26
    simpa using h
  have hprev := st42_p26
  have hstep := st42_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p28 : ((11454627853663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT42 (i+1))
      = (∑ i ∈ Finset.range 27, stT42 (i+1)) + stT42 28 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 27
    simpa using h
  have hprev := st42_p27
  have hstep := st42_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p29 : ((389791864207/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT42 (i+1))
      = (∑ i ∈ Finset.range 28, stT42 (i+1)) + stT42 29 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 28
    simpa using h
  have hprev := st42_p28
  have hstep := st42_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p30 : ((2550841536601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT42 (i+1))
      = (∑ i ∈ Finset.range 29, stT42 (i+1)) + stT42 30 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 29
    simpa using h
  have hprev := st42_p29
  have hstep := st42_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p31 : ((59980320597/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT42 (i+1))
      = (∑ i ∈ Finset.range 30, stT42 (i+1)) + stT42 31 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 30
    simpa using h
  have hprev := st42_p30
  have hstep := st42_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p32 : ((3076825134223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT42 (i+1))
      = (∑ i ∈ Finset.range 31, stT42 (i+1)) + stT42 32 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 31
    simpa using h
  have hprev := st42_p31
  have hstep := st42_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p33 : ((10743865193767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT42 (i+1))
      = (∑ i ∈ Finset.range 32, stT42 (i+1)) + stT42 33 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 32
    simpa using h
  have hprev := st42_p32
  have hstep := st42_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p34 : ((1909394606879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT42 (i+1))
      = (∑ i ∈ Finset.range 33, stT42 (i+1)) + stT42 34 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 33
    simpa using h
  have hprev := st42_p33
  have hstep := st42_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p35 : ((10274621893159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT42 (i+1))
      = (∑ i ∈ Finset.range 34, stT42 (i+1)) + stT42 35 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 34
    simpa using h
  have hprev := st42_p34
  have hstep := st42_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p36 : ((11938452894293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT42 (i+1))
      = (∑ i ∈ Finset.range 35, stT42 (i+1)) + stT42 36 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 35
    simpa using h
  have hprev := st42_p35
  have hstep := st42_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p37 : ((12521467289319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT42 (i+1))
      = (∑ i ∈ Finset.range 36, stT42 (i+1)) + stT42 37 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 36
    simpa using h
  have hprev := st42_p36
  have hstep := st42_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p38 : ((11406762252069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT42 (i+1))
      = (∑ i ∈ Finset.range 37, stT42 (i+1)) + stT42 38 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 37
    simpa using h
  have hprev := st42_p37
  have hstep := st42_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p39 : ((9866732491133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT42 (i+1))
      = (∑ i ∈ Finset.range 38, stT42 (i+1)) + stT42 39 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 38
    simpa using h
  have hprev := st42_p38
  have hstep := st42_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p40 : ((9506520566431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT42 (i+1))
      = (∑ i ∈ Finset.range 39, stT42 (i+1)) + stT42 40 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 39
    simpa using h
  have hprev := st42_p39
  have hstep := st42_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p41 : ((132933543191/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT42 (i+1))
      = (∑ i ∈ Finset.range 40, stT42 (i+1)) + stT42 41 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 40
    simpa using h
  have hprev := st42_p40
  have hstep := st42_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p42 : ((6065100148539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT42 (i+1))
      = (∑ i ∈ Finset.range 41, stT42 (i+1)) + stT42 42 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 41
    simpa using h
  have hprev := st42_p41
  have hstep := st42_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p43 : ((12629921106743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT42 (i+1))
      = (∑ i ∈ Finset.range 42, stT42 (i+1)) + stT42 43 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 42
    simpa using h
  have hprev := st42_p42
  have hstep := st42_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p44 : ((11739666486647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT42 (i+1))
      = (∑ i ∈ Finset.range 43, stT42 (i+1)) + stT42 44 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 43
    simpa using h
  have hprev := st42_p43
  have hstep := st42_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p45 : ((10248896348879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT42 (i+1))
      = (∑ i ∈ Finset.range 44, stT42 (i+1)) + stT42 45 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 44
    simpa using h
  have hprev := st42_p44
  have hstep := st42_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p46 : ((9364800205219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT42 (i+1))
      = (∑ i ∈ Finset.range 45, stT42 (i+1)) + stT42 46 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 45
    simpa using h
  have hprev := st42_p45
  have hstep := st42_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p47 : ((2435032388839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT42 (i+1))
      = (∑ i ∈ Finset.range 46, stT42 (i+1)) + stT42 47 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 46
    simpa using h
  have hprev := st42_p46
  have hstep := st42_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p48 : ((1381784538107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT42 (i+1))
      = (∑ i ∈ Finset.range 47, stT42 (i+1)) + stT42 48 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 47
    simpa using h
  have hprev := st42_p47
  have hstep := st42_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p49 : ((771678673389/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT42 (i+1))
      = (∑ i ∈ Finset.range 48, stT42 (i+1)) + stT42 49 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 48
    simpa using h
  have hprev := st42_p48
  have hstep := st42_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p50 : ((12741055091631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT42 (i+1))
      = (∑ i ∈ Finset.range 49, stT42 (i+1)) + stT42 50 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 49
    simpa using h
  have hprev := st42_p49
  have hstep := st42_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p51 : ((2402011599903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT42 (i+1))
      = (∑ i ∈ Finset.range 50, stT42 (i+1)) + stT42 51 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 50
    simpa using h
  have hprev := st42_p50
  have hstep := st42_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p52 : ((1065257437937/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT42 (i+1))
      = (∑ i ∈ Finset.range 51, stT42 (i+1)) + stT42 52 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 51
    simpa using h
  have hprev := st42_p51
  have hstep := st42_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p53 : ((4757079972951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT42 (i+1))
      = (∑ i ∈ Finset.range 52, stT42 (i+1)) + stT42 53 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 52
    simpa using h
  have hprev := st42_p52
  have hstep := st42_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p54 : ((925473305681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT42 (i+1))
      = (∑ i ∈ Finset.range 53, stT42 (i+1)) + stT42 54 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 53
    simpa using h
  have hprev := st42_p53
  have hstep := st42_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p55 : ((1998476294351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT42 (i+1))
      = (∑ i ∈ Finset.range 54, stT42 (i+1)) + stT42 55 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 54
    simpa using h
  have hprev := st42_p54
  have hstep := st42_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p56 : ((11291854869477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT42 (i+1))
      = (∑ i ∈ Finset.range 55, stT42 (i+1)) + stT42 56 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 55
    simpa using h
  have hprev := st42_p55
  have hstep := st42_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p57 : ((12448886552757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT42 (i+1))
      = (∑ i ∈ Finset.range 56, stT42 (i+1)) + stT42 57 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 56
    simpa using h
  have hprev := st42_p56
  have hstep := st42_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p58 : ((12876891581133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT42 (i+1))
      = (∑ i ∈ Finset.range 57, stT42 (i+1)) + stT42 58 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 57
    simpa using h
  have hprev := st42_p57
  have hstep := st42_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p59 : ((12386818524653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT42 (i+1))
      = (∑ i ∈ Finset.range 58, stT42 (i+1)) + stT42 59 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 58
    simpa using h
  have hprev := st42_p58
  have hstep := st42_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p60 : ((11241057880163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT42 (i+1))
      = (∑ i ∈ Finset.range 59, stT42 (i+1)) + stT42 60 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 59
    simpa using h
  have hprev := st42_p59
  have hstep := st42_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p61 : ((156096316483/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT42 (i+1))
      = (∑ i ∈ Finset.range 60, stT42 (i+1)) + stT42 61 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 60
    simpa using h
  have hprev := st42_p60
  have hstep := st42_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p62 : ((2299707137179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT42 (i+1))
      = (∑ i ∈ Finset.range 61, stT42 (i+1)) + stT42 62 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 61
    simpa using h
  have hprev := st42_p61
  have hstep := st42_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p63 : ((4598992843829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT42 (i+1))
      = (∑ i ∈ Finset.range 62, stT42 (i+1)) + stT42 63 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 62
    simpa using h
  have hprev := st42_p62
  have hstep := st42_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p64 : ((4982560343829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT42 (i+1))
      = (∑ i ∈ Finset.range 63, stT42 (i+1)) + stT42 64 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 63
    simpa using h
  have hprev := st42_p63
  have hstep := st42_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p65 : ((558204857691/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT42 (i+1))
      = (∑ i ∈ Finset.range 64, stT42 (i+1)) + stT42 65 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 64
    simpa using h
  have hprev := st42_p64
  have hstep := st42_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p66 : ((3076507710647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT42 (i+1))
      = (∑ i ∈ Finset.range 65, stT42 (i+1)) + stT42 66 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 65
    simpa using h
  have hprev := st42_p65
  have hstep := st42_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p67 : ((6475790030329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT42 (i+1))
      = (∑ i ∈ Finset.range 66, stT42 (i+1)) + stT42 67 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 66
    simpa using h
  have hprev := st42_p66
  have hstep := st42_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p68 : ((2574440346271/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT42 (i+1))
      = (∑ i ∈ Finset.range 67, stT42 (i+1)) + stT42 68 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 67
    simpa using h
  have hprev := st42_p67
  have hstep := st42_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p69 : ((12116472020951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT42 (i+1))
      = (∑ i ∈ Finset.range 68, stT42 (i+1)) + stT42 69 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 68
    simpa using h
  have hprev := st42_p68
  have hstep := st42_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p70 : ((10970364542393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT42 (i+1))
      = (∑ i ∈ Finset.range 69, stT42 (i+1)) + stT42 70 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 69
    simpa using h
  have hprev := st42_p69
  have hstep := st42_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p71 : ((9839330440061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT42 (i+1))
      = (∑ i ∈ Finset.range 70, stT42 (i+1)) + stT42 71 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 70
    simpa using h
  have hprev := st42_p70
  have hstep := st42_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p72 : ((9102376245149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT42 (i+1))
      = (∑ i ∈ Finset.range 71, stT42 (i+1)) + stT42 72 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 71
    simpa using h
  have hprev := st42_p71
  have hstep := st42_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p73 : ((8989937105133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT42 (i+1))
      = (∑ i ∈ Finset.range 72, stT42 (i+1)) + stT42 73 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 72
    simpa using h
  have hprev := st42_p72
  have hstep := st42_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p74 : ((9521804749413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT42 (i+1))
      = (∑ i ∈ Finset.range 73, stT42 (i+1)) + stT42 74 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 73
    simpa using h
  have hprev := st42_p73
  have hstep := st42_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p75 : ((10517002574313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT42 (i+1))
      = (∑ i ∈ Finset.range 74, stT42 (i+1)) + stT42 75 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 74
    simpa using h
  have hprev := st42_p74
  have hstep := st42_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p76 : ((2332735589987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT42 (i+1))
      = (∑ i ∈ Finset.range 75, stT42 (i+1)) + stT42 76 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 75
    simpa using h
  have hprev := st42_p75
  have hstep := st42_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p77 : ((2524170996307/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT42 (i+1))
      = (∑ i ∈ Finset.range 76, stT42 (i+1)) + stT42 77 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 76
    simpa using h
  have hprev := st42_p76
  have hstep := st42_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p78 : ((13118680945571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT42 (i+1))
      = (∑ i ∈ Finset.range 77, stT42 (i+1)) + stT42 78 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 77
    simpa using h
  have hprev := st42_p77
  have hstep := st42_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p79 : ((13028988930211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT42 (i+1))
      = (∑ i ∈ Finset.range 78, stT42 (i+1)) + stT42 79 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 78
    simpa using h
  have hprev := st42_p78
  have hstep := st42_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p80 : ((495608947321/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT42 (i+1))
      = (∑ i ∈ Finset.range 79, stT42 (i+1)) + stT42 80 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 79
    simpa using h
  have hprev := st42_p79
  have hstep := st42_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p81 : ((11385355101353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT42 (i+1))
      = (∑ i ∈ Finset.range 80, stT42 (i+1)) + stT42 81 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 80
    simpa using h
  have hprev := st42_p80
  have hstep := st42_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p82 : ((10284035110661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT42 (i+1))
      = (∑ i ∈ Finset.range 81, stT42 (i+1)) + stT42 82 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 81
    simpa using h
  have hprev := st42_p81
  have hstep := st42_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p83 : ((1170990724777/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT42 (i+1))
      = (∑ i ∈ Finset.range 82, stT42 (i+1)) + stT42 83 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 82
    simpa using h
  have hprev := st42_p82
  have hstep := st42_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p84 : ((4429915140143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT42 (i+1))
      = (∑ i ∈ Finset.range 83, stT42 (i+1)) + stT42 84 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 83
    simpa using h
  have hprev := st42_p83
  have hstep := st42_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p85 : ((4436777733347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT42 (i+1))
      = (∑ i ∈ Finset.range 84, stT42 (i+1)) + stT42 85 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 84
    simpa using h
  have hprev := st42_p84
  have hstep := st42_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p86 : ((187884038709/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT42 (i+1))
      = (∑ i ∈ Finset.range 85, stT42 (i+1)) + stT42 86 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 85
    simpa using h
  have hprev := st42_p85
  have hstep := st42_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p87 : ((5145081894813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT42 (i+1))
      = (∑ i ∈ Finset.range 86, stT42 (i+1)) + stT42 87 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 86
    simpa using h
  have hprev := st42_p86
  have hstep := st42_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p88 : ((5675324579049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT42 (i+1))
      = (∑ i ∈ Finset.range 87, stT42 (i+1)) + stT42 88 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 87
    simpa using h
  have hprev := st42_p87
  have hstep := st42_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p89 : ((12337596464843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT42 (i+1))
      = (∑ i ∈ Finset.range 88, stT42 (i+1)) + stT42 89 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 88
    simpa using h
  have hprev := st42_p88
  have hstep := st42_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p90 : ((13039097853119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT42 (i+1))
      = (∑ i ∈ Finset.range 89, stT42 (i+1)) + stT42 90 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 89
    simpa using h
  have hprev := st42_p89
  have hstep := st42_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p91 : ((13312731425639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT42 (i+1))
      = (∑ i ∈ Finset.range 90, stT42 (i+1)) + stT42 91 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 90
    simpa using h
  have hprev := st42_p90
  have hstep := st42_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p92 : ((2622157424137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT42 (i+1))
      = (∑ i ∈ Finset.range 91, stT42 (i+1)) + stT42 92 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 91
    simpa using h
  have hprev := st42_p91
  have hstep := st42_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p93 : ((12484062664453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT42 (i+1))
      = (∑ i ∈ Finset.range 92, stT42 (i+1)) + stT42 93 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 92
    simpa using h
  have hprev := st42_p92
  have hstep := st42_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p94 : ((11565672138589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT42 (i+1))
      = (∑ i ∈ Finset.range 93, stT42 (i+1)) + stT42 94 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 93
    simpa using h
  have hprev := st42_p93
  have hstep := st42_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p95 : ((10540050179281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT42 (i+1))
      = (∑ i ∈ Finset.range 94, stT42 (i+1)) + stT42 95 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 94
    simpa using h
  have hprev := st42_p94
  have hstep := st42_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p96 : ((2401153317451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT42 (i+1))
      = (∑ i ∈ Finset.range 95, stT42 (i+1)) + stT42 96 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 95
    simpa using h
  have hprev := st42_p95
  have hstep := st42_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p97 : ((2233007792863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT42 (i+1))
      = (∑ i ∈ Finset.range 96, stT42 (i+1)) + stT42 97 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 96
    simpa using h
  have hprev := st42_p96
  have hstep := st42_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p98 : ((4320015142177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT42 (i+1))
      = (∑ i ∈ Finset.range 97, stT42 (i+1)) + stT42 98 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 97
    simpa using h
  have hprev := st42_p97
  have hstep := st42_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p99 : ((8773455981363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT42 (i+1))
      = (∑ i ∈ Finset.range 98, stT42 (i+1)) + stT42 99 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 98
    simpa using h
  have hprev := st42_p98
  have hstep := st42_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st42_p100 : ((4650308227101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT42 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT42 (i+1))
      = (∑ i ∈ Finset.range 99, stT42 (i+1)) + stT42 100 := by
    have h := Finset.sum_range_succ (fun i => stT42 (i+1)) 99
    simpa using h
  have hprev := st42_p99
  have hstep := st42_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 42`.** -/
theorem station_42_sign : 0 < hardyG (((42:ℕ)):ℝ) := by
  have hcore := phase_station_lower 42 100 (by norm_num) (by norm_num)
    ((-69223/200000 : ℚ) : ℝ)
  have hchain := st42_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT42 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((42:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-69223/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((42:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((42:ℕ)):ℝ)+1) * ((((42:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1882133/4200000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((4650308227101/5000000000000 : ℚ) : ℝ) - ((1882133/4200000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-69223/200000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((42:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-69223/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((42:ℕ)):ℝ))).re
      - Real.sin ((-69223/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((42:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((42:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((42:ℕ)):ℝ)
      = ((((42:ℕ)):ℝ) * (Real.log (((42:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((42:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_42
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
  have hθwin : |(((-69223/200000 : ℚ) : ℝ) + ((3:ℤ)) * (2*Real.pi)) - theta (((42:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((42:ℕ)):ℝ))
    (φ := ((-69223/200000 : ℚ) : ℝ) + ((3:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-69223/200000 : ℚ)) : ℝ) 3).1,
    (cos_sin_shift (((-69223/200000 : ℚ)) : ℝ) 3).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_42_sign
end AxiomAudit
