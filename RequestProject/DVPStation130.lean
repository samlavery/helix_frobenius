import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 130` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT130 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((130 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))

theorem st130_c1 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((921601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62283/625000) (δ := 201/1000000000) (ψ := -398611/1000000) 130 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t1 : ((921551/1000000 : ℚ) : ℝ) ≤ stT130 1 := by
  have hc : ((921551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((921551/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((921551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c2 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-206553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271573/2000000) (δ := 6701/1000000000) (ψ := -398611/1000000) 130 14
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t2 : ((-730319348477/1250000000000 : ℚ) : ℝ) ≤ stT130 2 := by
  have hc : ((-413131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-730319348477/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-413131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c3 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((272257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1618823/5000000) (δ := 6667/1000000000) (ψ := -398611/1000000) 130 23
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t3 : ((785793829457/5000000000000 : ℚ) : ℝ) ≤ stT130 3 := by
  have hc : ((272207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((785793829457/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((272207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c4 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-24699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -498593/1250000) (δ := 6693/1000000000) (ψ := -398611/1000000) 130 29
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t4 : ((-123745024749/10000000000000 : ℚ) : ℝ) ≤ stT130 4 := by
  have hc : ((-24749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123745024749/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-24749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c5 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-130311/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5701073/10000000) (δ := 1333/200000000) (ψ := -398611/1000000) 130 33
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t5 : ((-72851654457/250000000000 : ℚ) : ℝ) ≤ stT130 5 := by
  have hc : ((-130321/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72851654457/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-130321/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c6 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((660371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530927/2500000) (δ := 6567/1000000000) (ψ := -398611/1000000) 130 37
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t6 : ((1347874298361/5000000000000 : ℚ) : ℝ) ≤ stT130 6 := by
  have hc : ((660321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1347874298361/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((660321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c7 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-451747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1274699/2500000) (δ := 6689/1000000000) (ψ := -398611/1000000) 130 40
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t7 : ((-341526454413/2000000000000 : ℚ) : ℝ) ≤ stT130 7 := by
  have hc : ((-451797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341526454413/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-451797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c8 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((26657/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1372611/10000000) (δ := 661/100000000) (ψ := -398611/1000000) 130 43
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t8 : ((1507858862571/5000000000000 : ℚ) : ℝ) ≤ stT130 8 := by
  have hc : ((426487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1507858862571/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((426487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c9 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-494169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1867951/2500000) (δ := 1633/250000000) (ψ := -398611/1000000) 130 46
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t9 : ((-411828415699/1250000000000 : ℚ) : ℝ) ≤ stT130 9 := by
  have hc : ((-247097/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411828415699/1250000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-247097/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c10 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-283489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72587/156250) (δ := 3273/500000000) (ψ := -398611/1000000) 130 48
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t10 : ((-448314570921/5000000000000 : ℚ) : ℝ) ≤ stT130 10 := by
  have hc : ((-283539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448314570921/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-283539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c11 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-22353/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63571/125000) (δ := 6643/1000000000) (ψ := -398611/1000000) 130 50
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t11 : ((-67404381027/500000000000 : ℚ) : ℝ) ≤ stT130 11 := by
  have hc : ((-44711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67404381027/500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-44711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c12 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-247283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3742531/5000000) (δ := 1307/200000000) (ψ := -398611/1000000) 130 51
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t12 : ((-44617548701/156250000000 : ℚ) : ℝ) ≤ stT130 12 := by
  have hc : ((-494591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44617548701/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-494591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c13 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((672507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2083013/10000000) (δ := 6521/1000000000) (ψ := -398611/1000000) 130 53
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t13 : ((3730118979/20000000000 : ℚ) : ℝ) ≤ stT130 13 := by
  have hc : ((672457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3730118979/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((672457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c14 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-504091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5247813/10000000) (δ := 837/125000000) (ψ := -398611/1000000) 130 55
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t14 : ((-1347373790433/10000000000000 : ℚ) : ℝ) ≤ stT130 14 := by
  have hc : ((-504141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1347373790433/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-504141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c15 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((166547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 366729/2500000) (δ := 1651/250000000) (ψ := -398611/1000000) 130 56
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t15 : ((107499133889/500000000000 : ℚ) : ℝ) ≤ stT130 15 := by
  have hc : ((166537/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107499133889/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((166537/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c16 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-14083/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1346793/2000000) (δ := 6511/1000000000) (ψ := -398611/1000000) 130 57
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t16 : ((-1126702950681/5000000000000 : ℚ) : ℝ) ≤ stT130 16 := by
  have hc : ((-450681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1126702950681/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-450681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c17 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-204241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4978967/10000000) (δ := 3339/500000000) (ψ := -398611/1000000) 130 59
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t17 : ((-247708986481/2500000000000 : ℚ) : ℝ) ≤ stT130 17 := by
  have hc : ((-102133/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247708986481/2500000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-102133/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c18 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((83043/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42209/200000) (δ := 6571/1000000000) (ψ := -398611/1000000) 130 60
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t18 : ((391438893117/2500000000000 : ℚ) : ℝ) ≤ stT130 18 := by
  have hc : ((332147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391438893117/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((332147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c19 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((49757/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246573/10000000) (δ := 6539/1000000000) (ψ := -398611/1000000) 130 61
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t19 : ((228289268913/1000000000000 : ℚ) : ℝ) ≤ stT130 19 := by
  have hc : ((99509/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228289268913/1000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((99509/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c20 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((959291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357893/5000000) (δ := 1639/250000000) (ψ := -398611/1000000) 130 62
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t20 : ((2144927145147/10000000000000 : ℚ) : ℝ) ≤ stT130 20 := by
  have hc : ((959241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2144927145147/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((959241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c21 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((470393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432319/5000000) (δ := 3277/500000000) (ψ := -398611/1000000) 130 63
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t21 : ((16037917211/78125000000 : ℚ) : ℝ) ≤ stT130 21 := by
  have hc : ((14699/15625 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16037917211/78125000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((14699/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c22 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((496963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11027/400000) (δ := 6661/1000000000) (ψ := -398611/1000000) 130 64
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t22 : ((529737647283/2500000000000 : ℚ) : ℝ) ≤ stT130 22 := by
  have hc : ((248469/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529737647283/2500000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((248469/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c23 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((923311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -492727/5000000) (δ := 1327/200000000) (ψ := -398611/1000000) 130 65
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t23 : ((240641516823/1250000000000 : ℚ) : ℝ) ≤ stT130 23 := by
  have hc : ((923261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240641516823/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((923261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c24 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((413393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2861547/10000000) (δ := 51/7812500) (ψ := -398611/1000000) 130 66
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t24 : ((843732678663/10000000000000 : ℚ) : ℝ) ≤ stT130 24 := by
  have hc : ((413343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((843732678663/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((413343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c25 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-522813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132559/250000) (δ := 6583/1000000000) (ψ := -398611/1000000) 130 67
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t25 : ((-1045726522863/10000000000000 : ℚ) : ℝ) ≤ stT130 25 := by
  have hc : ((-522863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1045726522863/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-522863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c26 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-986607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7444367/10000000) (δ := 331/50000000) (ψ := -398611/1000000) 130 67
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t26 : ((-967497107717/5000000000000 : ℚ) : ℝ) ≤ stT130 26 := by
  have hc : ((-986657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-967497107717/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-986657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c27 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-3/100 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2001001/5000000) (δ := 669/100000000) (ψ := -398611/1000000) 130 68
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t27 : ((-1156625101/200000000000 : ℚ) : ℝ) ≤ stT130 27 := by
  have hc : ((-601/20000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1156625101/200000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-601/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c28 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((998969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113541/10000000) (δ := 6597/1000000000) (ψ := -398611/1000000) 130 69
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t28 : ((943889551209/5000000000000 : ℚ) : ℝ) ≤ stT130 28 := by
  have hc : ((998919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((943889551209/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((998919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c29 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-10491/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16759/40000) (δ := 813/125000000) (ψ := -398611/1000000) 130 70
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t29 : ((-38067557/1953125000 : ℚ) : ℝ) ≤ stT130 29 := by
  have hc : ((-328/3125 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38067557/1953125000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-328/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c30 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-458501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6828237/10000000) (δ := 6699/1000000000) (ψ := -398611/1000000) 130 70
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t30 : ((-209287544073/1250000000000 : ℚ) : ℝ) ≤ stT130 30 := by
  have hc : ((-229263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209287544073/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-229263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c31 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((378921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55531/312500) (δ := 6611/1000000000) (ψ := -398611/1000000) 130 71
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t31 : ((42532331093/312500000000 : ℚ) : ℝ) ≤ stT130 31 := by
  have hc : ((23681/31250 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42532331093/312500000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((23681/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c32 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((3919/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -903161/2500000) (δ := 3259/500000000) (ψ := -398611/1000000) 130 72
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t32 : ((55400902557/2500000000000 : ℚ) : ℝ) ≤ stT130 32 := by
  have hc : ((62679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55400902557/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((62679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c33 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-83297/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3194063/5000000) (δ := 3259/500000000) (ψ := -398611/1000000) 130 72
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t33 : ((-72505102827/500000000000 : ℚ) : ℝ) ≤ stT130 33 := by
  have hc : ((-41651/50000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72505102827/500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-41651/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c34 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((39533/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95597/2500000) (δ := 3313/500000000) (ψ := -398611/1000000) 130 73
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t34 : ((13559014407/80000000000 : ℚ) : ℝ) ≤ stT130 34 := by
  have hc : ((39531/40000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13559014407/80000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((39531/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c35 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-355549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2952319/5000000) (δ := 6533/1000000000) (ψ := -398611/1000000) 130 74
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t35 : ((-300514966183/2500000000000 : ℚ) : ℝ) ≤ stT130 35 := by
  have hc : ((-177787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300514966183/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-177787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c36 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((5343/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 406363/1250000) (δ := 667/100000000) (ψ := -398611/1000000) 130 74
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t36 : ((2225832443/50000000000 : ℚ) : ℝ) ≤ stT130 36 := by
  have hc : ((2671/10000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2225832443/50000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((2671/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c37 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((149283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27753/78125) (δ := 6563/1000000000) (ψ := -398611/1000000) 130 75
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t37 : ((245337410437/10000000000000 : ℚ) : ℝ) ≤ stT130 37 := by
  have hc : ((149233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245337410437/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((149233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c38 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-228721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5114781/10000000) (δ := 6563/1000000000) (ψ := -398611/1000000) 130 75
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t38 : ((-37107519239/500000000000 : ℚ) : ℝ) ≤ stT130 38 := by
  have hc : ((-114373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37107519239/500000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-114373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c39 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((65209/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430229/2000000) (δ := 13/1953125) (ψ := -398611/1000000) 130 76
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t39 : ((26102481581/250000000000 : ℚ) : ℝ) ≤ stT130 39 := by
  have hc : ((16301/25000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26102481581/250000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((16301/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c40 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-757881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303857/500000) (δ := 13/1953125) (ψ := -398611/1000000) 130 76
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t40 : ((-1198394263409/10000000000000 : ℚ) : ℝ) ≤ stT130 40 := by
  have hc : ((-757931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1198394263409/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-757931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c41 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((32029/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50179/312500) (δ := 6549/1000000000) (ψ := -398611/1000000) 130 77
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t41 : ((50017750899/400000000000 : ℚ) : ℝ) ≤ stT130 41 := by
  have hc : ((32027/40000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50017750899/400000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((32027/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c42 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-4971/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778249/1250000) (δ := 6549/1000000000) (ψ := -398611/1000000) 130 77
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t42 : ((-61367233697/500000000000 : ℚ) : ℝ) ≤ stT130 42 := by
  have hc : ((-79541/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61367233697/500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-79541/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c43 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((742619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834559/10000000) (δ := 6641/1000000000) (ψ := -398611/1000000) 130 78
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t43 : ((226481317293/2000000000000 : ℚ) : ℝ) ≤ stT130 43 := by
  have hc : ((742569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226481317293/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((742569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c44 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-63191/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5637029/10000000) (δ := 3281/500000000) (ψ := -398611/1000000) 130 78
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t44 : ((-23817893043/250000000000 : ℚ) : ℝ) ≤ stT130 44 := by
  have hc : ((-15799/25000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23817893043/250000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-15799/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c45 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((447427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1383637/5000000) (δ := 6669/1000000000) (ψ := -398611/1000000) 130 79
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t45 : ((666909815047/10000000000000 : ℚ) : ℝ) ≤ stT130 45 := by
  have hc : ((447377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((666909815047/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((447377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c46 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-44647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1093967/2500000) (δ := 3267/500000000) (ψ := -398611/1000000) 130 79
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t46 : ((-6584685999/250000000000 : ℚ) : ℝ) ≤ stT130 46 := by
  have hc : ((-89319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6584685999/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-89319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c47 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-82729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1085637/2500000) (δ := 6627/1000000000) (ψ := -398611/1000000) 130 80
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t47 : ((-1207091221/50000000000 : ℚ) : ℝ) ≤ stT130 47 := by
  have hc : ((-41377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1207091221/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-41377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c48 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((540367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2499807/10000000) (δ := 6627/1000000000) (ψ := -398611/1000000) 130 80
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t48 : ((6239040399/80000000000 : ℚ) : ℝ) ≤ stT130 48 := by
  have hc : ((540317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6239040399/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((540317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c49 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-107289/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1626729/2500000) (δ := 163/25000000) (ψ := -398611/1000000) 130 81
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t49 : ((-153278989883/1250000000000 : ℚ) : ℝ) ≤ stT130 49 := by
  have hc : ((-429181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153278989883/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-429181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c50 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((499861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29497/5000000) (δ := 163/25000000) (ψ := -398611/1000000) 130 81
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t50 : ((176718642267/1250000000000 : ℚ) : ℝ) ≤ stT130 50 := by
  have hc : ((124959/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176718642267/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((124959/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c51 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-855823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6494839/10000000) (δ := 163/25000000) (ψ := -398611/1000000) 130 81
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t51 : ((-1198462700313/10000000000000 : ℚ) : ℝ) ≤ stT130 51 := by
  have hc : ((-855873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1198462700313/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-855873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c52 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((398517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1451121/5000000) (δ := 6613/1000000000) (ψ := -398611/1000000) 130 82
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t52 : ((2210296449/40000000000 : ℚ) : ℝ) ≤ stT130 52 := by
  have hc : ((398467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2210296449/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((398467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c53 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((252659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3288423/10000000) (δ := 6613/1000000000) (ψ := -398611/1000000) 130 82
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t53 : ((69396997089/2000000000000 : ℚ) : ℝ) ≤ stT130 53 := by
  have hc : ((252609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69396997089/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((252609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c54 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-205803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6344607/10000000) (δ := 6697/1000000000) (ψ := -398611/1000000) 130 83
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t54 : ((-140039747617/1250000000000 : ℚ) : ℝ) ≤ stT130 54 := by
  have hc : ((-411631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140039747617/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-411631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c55 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((2471/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7623/200000) (δ := 3253/500000000) (ψ := -398611/1000000) 130 83
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t55 : ((26653803033/200000000000 : ℚ) : ℝ) ≤ stT130 55 := by
  have hc : ((19767/20000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26653803033/200000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((19767/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c56 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-290171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5474863/10000000) (δ := 6697/1000000000) (ψ := -398611/1000000) 130 83
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t56 : ((-96947736543/1250000000000 : ℚ) : ℝ) ≤ stT130 56 := by
  have hc : ((-72549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96947736543/1250000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-72549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c57 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-219689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4480731/10000000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 84
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t57 : ((-291051556887/10000000000000 : ℚ) : ℝ) ≤ stT130 57 := by
  have hc : ((-219739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291051556887/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-219739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c58 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((892183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292901/2500000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 84
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t58 : ((146428465689/1250000000000 : ℚ) : ℝ) ≤ stT130 58 := by
  have hc : ((892133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146428465689/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((892133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c59 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-112519/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1681821/2500000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 84
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t59 : ((-58598199089/500000000000 : ℚ) : ℝ) ≤ stT130 59 := by
  have hc : ((-450101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58598199089/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-450101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c60 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((162721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -879593/2500000) (δ := 6691/1000000000) (ψ := -398611/1000000) 130 85
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t60 : ((105003642487/5000000000000 : ℚ) : ℝ) ≤ stT130 60 := by
  have hc : ((162671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105003642487/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((162671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c61 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((737483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1853651/10000000) (δ := 407/62500000) (ψ := -398611/1000000) 130 85
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t61 : ((59011600959/625000000000 : ℚ) : ℝ) ≤ stT130 61 := by
  have hc : ((737433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59011600959/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((737433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c62 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-191861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7138313/10000000) (δ := 6691/1000000000) (ψ := -398611/1000000) 130 85
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t62 : ((-121838276871/1000000000000 : ℚ) : ℝ) ≤ stT130 62 := by
  have hc : ((-191871/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121838276871/1000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-191871/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c63 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((44229/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42119/125000) (δ := 823/125000000) (ψ := -398611/1000000) 130 86
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t63 : ((55710677939/2000000000000 : ℚ) : ℝ) ≤ stT130 63 := by
  have hc : ((44219/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55710677939/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((44219/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c64 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((765183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 874339/5000000) (δ := 6619/1000000000) (ψ := -398611/1000000) 130 86
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t64 : ((765133/8000000 : ℚ) : ℝ) ≤ stT130 64 := by
  have hc : ((765133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((765133/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((765133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c65 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-227597/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6787543/10000000) (δ := 6619/1000000000) (ψ := -398611/1000000) 130 86
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t65 : ((-141157494053/1250000000000 : ℚ) : ℝ) ≤ stT130 65 := by
  have hc : ((-455219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141157494053/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-455219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c66 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-12597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3958483/10000000) (δ := 3263/500000000) (ψ := -398611/1000000) 130 87
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t66 : ((-3113476401/2000000000000 : ℚ) : ℝ) ≤ stT130 66 := by
  have hc : ((-12647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3113476401/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-12647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c67 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((232943/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464417/5000000) (δ := 6677/1000000000) (ψ := -398611/1000000) 130 87
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t67 : ((284569794267/2500000000000 : ℚ) : ℝ) ≤ stT130 67 := by
  have hc : ((465861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284569794267/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((465861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c68 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-664407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2871871/5000000) (δ := 3263/500000000) (ψ := -398611/1000000) 130 87
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t68 : ((-805773050303/10000000000000 : ℚ) : ℝ) ≤ stT130 68 := by
  have hc : ((-664457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-805773050303/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-664457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c69 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-123579/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5219611/10000000) (δ := 6633/1000000000) (ψ := -398611/1000000) 130 88
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t69 : ((-297573479197/5000000000000 : ℚ) : ℝ) ≤ stT130 69 := by
  have hc : ((-247183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297573479197/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-247183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c70 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((6103/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135821/2500000) (δ := 657/100000000) (ψ := -398611/1000000) 130 88
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t70 : ((29176411901/250000000000 : ℚ) : ℝ) ≤ stT130 70 := by
  have hc : ((97643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29176411901/250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((97643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c71 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-55859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4066711/10000000) (δ := 657/100000000) (ψ := -398611/1000000) 130 88
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t71 : ((-33175897419/5000000000000 : ℚ) : ℝ) ≤ stT130 71 := by
  have hc : ((-55909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33175897419/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-55909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c72 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-954353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1419141/2000000) (δ := 6663/1000000000) (ψ := -398611/1000000) 130 89
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t72 : ((-70298461771/625000000000 : ℚ) : ℝ) ≤ stT130 72 := by
  have hc : ((-954403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70298461771/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-954403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c73 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((50177/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1306441/5000000) (δ := 327/50000000) (ψ := -398611/1000000) 130 89
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t73 : ((14680465173/250000000000 : ℚ) : ℝ) ≤ stT130 73 := by
  have hc : ((12543/25000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14680465173/250000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((12543/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c74 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((749443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904469/5000000) (δ := 327/50000000) (ψ := -398611/1000000) 130 89
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t74 : ((217787844267/2500000000000 : ℚ) : ℝ) ≤ stT130 74 := by
  have hc : ((749393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217787844267/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((749393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c75 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-390973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1234289/2000000) (δ := 6663/1000000000) (ψ := -398611/1000000) 130 89
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t75 : ((-225742890799/2500000000000 : ℚ) : ℝ) ≤ stT130 75 := by
  have hc : ((-195499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225742890799/2500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-195499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c76 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-249279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1307957/2500000) (δ := 1311/200000000) (ψ := -398611/1000000) 130 90
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t76 : ((-35746422877/625000000000 : ℚ) : ℝ) ≤ stT130 76 := by
  have hc : ((-31163/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35746422877/625000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-31163/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c77 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((923627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196679/2000000) (δ := 831/125000000) (ψ := -398611/1000000) 130 90
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t77 : ((210502593417/2000000000000 : ℚ) : ℝ) ≤ stT130 77 := by
  have hc : ((923577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210502593417/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((923577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c78 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((707/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321021/1000000) (δ := 831/125000000) (ψ := -398611/1000000) 130 90
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t78 : ((1280605287/40000000000 : ℚ) : ℝ) ≤ stT130 78 := by
  have hc : ((1131/4000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1280605287/40000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((1131/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c79 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-48989/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1470077/2000000) (δ := 831/125000000) (ψ := -398611/1000000) 130 90
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t79 : ((-3444984297/31250000000 : ℚ) : ℝ) ≤ stT130 79 := by
  have hc : ((-97983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3444984297/31250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-97983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c80 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-136563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4269469/10000000) (δ := 831/125000000) (ψ := -398611/1000000) 130 91
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t80 : ((-76368989421/5000000000000 : ℚ) : ℝ) ≤ stT130 80 := by
  have hc : ((-136613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76368989421/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-136613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c81 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((995691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58039/2500000) (δ := 1311/200000000) (ψ := -398611/1000000) 130 91
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t81 : ((1106267667151/10000000000000 : ℚ) : ℝ) ≤ stT130 81 := by
  have hc : ((995641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1106267667151/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((995641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c82 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((17123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1877813/5000000) (δ := 831/125000000) (ψ := -398611/1000000) 130 91
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t82 : ((7558152723/1000000000000 : ℚ) : ℝ) ≤ stT130 82 := by
  have hc : ((34221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7558152723/1000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((34221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c83 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-997981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7695081/10000000) (δ := 831/125000000) (ψ := -398611/1000000) 130 91
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t83 : ((-1095481740933/10000000000000 : ℚ) : ℝ) ≤ stT130 83 := by
  have hc : ((-998031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1095481740933/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-998031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c84 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-77379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4120633/10000000) (δ := 6531/500000000) (ψ := -398611/1000000) 130 92
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t84 : ((-8448200761/1000000000000 : ℚ) : ℝ) ≤ stT130 84 := by
  have hc : ((-77429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8448200761/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-77429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c85 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((993981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274437/10000000) (δ := 6541/1000000000) (ψ := -398611/1000000) 130 92
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t85 : ((269517311753/2500000000000 : ℚ) : ℝ) ≤ stT130 85 := by
  have hc : ((993931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269517311753/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((993931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c86 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((9963/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3526763/10000000) (δ := 6541/1000000000) (ψ := -398611/1000000) 130 92
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t86 : ((85920017033/5000000000000 : ℚ) : ℝ) ≤ stT130 86 := by
  have hc : ((79679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85920017033/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((79679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c87 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-974127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910507/1250000) (δ := 3331/500000000) (ψ := -398611/1000000) 130 92
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t87 : ((-1044427826001/10000000000000 : ℚ) : ℝ) ≤ stT130 87 := by
  have hc : ((-974177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1044427826001/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-974177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c88 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-76987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235479/500000) (δ := 6569/1000000000) (ψ := -398611/1000000) 130 93
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t88 : ((-41040887499/1250000000000 : ℚ) : ℝ) ≤ stT130 88 := by
  have hc : ((-153999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41040887499/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-153999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c89 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((457579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1037243/10000000) (δ := 3317/500000000) (ψ := -398611/1000000) 130 93
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t89 : ((242502933669/2500000000000 : ℚ) : ℝ) ≤ stT130 89 := by
  have hc : ((228777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242502933669/2500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((228777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c90 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((508261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16213/62500) (δ := 6569/1000000000) (ψ := -398611/1000000) 130 93
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t90 : ((133925287353/2500000000000 : ℚ) : ℝ) ≤ stT130 90 := by
  have hc : ((508211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133925287353/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((508211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c91 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-98173/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6185281/10000000) (δ := 6517/500000000) (ψ := -398611/1000000) 130 93
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t91 : ((-82335868069/1000000000000 : ℚ) : ℝ) ≤ stT130 91 := by
  have hc : ((-392717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82335868069/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-392717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c92 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-364719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5970741/10000000) (δ := 6527/1000000000) (ψ := -398611/1000000) 130 94
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t92 : ((-47534030789/625000000000 : ℚ) : ℝ) ≤ stT130 92 := by
  have hc : ((-45593/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47534030789/625000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-45593/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c93 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((554629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1228599/5000000) (δ := 1669/250000000) (ψ := -398611/1000000) 130 94
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t93 : ((575071248629/10000000000000 : ℚ) : ℝ) ≤ stT130 93 := by
  have hc : ((554579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((575071248629/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((554579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c94 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((918111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 509387/5000000) (δ := 6527/1000000000) (ψ := -398611/1000000) 130 94
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t94 : ((946907394681/10000000000000 : ℚ) : ℝ) ≤ stT130 94 := by
  have hc : ((918061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((946907394681/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((918061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c95 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-210793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4457957/10000000) (δ := 1669/250000000) (ψ := -398611/1000000) 130 94
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t95 : ((-216320490297/10000000000000 : ℚ) : ℝ) ≤ stT130 95 := by
  have hc : ((-210843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216320490297/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-210843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c96 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3923417/5000000) (δ := 823/125000000) (ψ := -398611/1000000) 130 95
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t96 : ((-510333974283/5000000000000 : ℚ) : ℝ) ≤ stT130 96 := by
  have hc : ((-500023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-510333974283/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-500023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c97 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-27373/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1119731/2500000) (δ := 823/125000000) (ψ := -398611/1000000) 130 95
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t97 : ((-111197757399/5000000000000 : ℚ) : ℝ) ≤ stT130 97 := by
  have hc : ((-109517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111197757399/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-109517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c98 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((896839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -572781/5000000) (δ := 6619/1000000000) (ψ := -398611/1000000) 130 95
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t98 : ((113236650241/1250000000000 : ℚ) : ℝ) ≤ stT130 98 := by
  have hc : ((896789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113236650241/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((896789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c99 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((325617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134623/625000) (δ := 6619/1000000000) (ψ := -398611/1000000) 130 95
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t99 : ((40904000863/625000000000 : ℚ) : ℝ) ≤ stT130 99 := by
  have hc : ((40699/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40904000863/625000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((40699/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c100 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-562437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1355079/2500000) (δ := 823/125000000) (ψ := -398611/1000000) 130 95
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t100 : ((-562487/10000000 : ℚ) : ℝ) ≤ stT130 100 := by
  have hc : ((-562487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562487/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-562487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c101 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-118651/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7053767/10000000) (δ := 6691/1000000000) (ψ := -398611/1000000) 130 96
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t101 : ((-236136945451/2500000000000 : ℚ) : ℝ) ≤ stT130 101 := by
  have hc : ((-474629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236136945451/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-474629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c102 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((7521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -385177/1000000) (δ := 407/62500000) (ψ := -398611/1000000) 130 96
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t102 : ((14869037499/5000000000000 : ℚ) : ℝ) ≤ stT130 102 := by
  have hc : ((15017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14869037499/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((15017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c103 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((240781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681037/10000000) (δ := 6691/1000000000) (ψ := -398611/1000000) 130 96
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t103 : ((474472370673/5000000000000 : ℚ) : ℝ) ≤ stT130 103 := by
  have hc : ((481537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474472370673/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((481537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c104 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((554003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61477/250000) (δ := 407/62500000) (ψ := -398611/1000000) 130 96
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t104 : ((27159761637/500000000000 : ℚ) : ℝ) ≤ stT130 104 := by
  have hc : ((553953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27159761637/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((553953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c105 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-305321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348073/625000) (δ := 6691/1000000000) (ψ := -398611/1000000) 130 96
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t105 : ((-148993733373/2500000000000 : ℚ) : ℝ) ≤ stT130 105 := by
  have hc : ((-152673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148993733373/2500000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-152673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c106 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-949767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3529109/5000000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 97
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t106 : ((-461271977331/5000000000000 : ℚ) : ℝ) ≤ stT130 106 := by
  have hc : ((-949817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461271977331/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-949817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c107 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-7953/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4006533/10000000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 97
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t107 : ((-15401087147/5000000000000 : ℚ) : ℝ) ≤ stT130 107 := by
  have hc : ((-15931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15401087147/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-15931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c108 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((923649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -983253/10000000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 97
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t108 : ((3554932551/40000000000 : ℚ) : ℝ) ≤ stT130 108 := by
  have hc : ((923599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3554932551/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((923599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c109 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((346607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1006071/5000000) (δ := 3299/500000000) (ψ := -398611/1000000) 130 97
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t109 : ((82991312683/1250000000000 : ℚ) : ℝ) ≤ stT130 109 := by
  have hc : ((173291/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82991312683/1250000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((173291/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c110 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-204467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1245051/2500000) (δ := 1321/200000000) (ψ := -398611/1000000) 130 97
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t110 : ((-48743888949/1250000000000 : ℚ) : ℝ) ≤ stT130 110 := by
  have hc : ((-51123/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48743888949/1250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-51123/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c111 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-249909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3893271/5000000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 98
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t111 : ((-237214991097/2500000000000 : ℚ) : ℝ) ≤ stT130 111 := by
  have hc : ((-499843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237214991097/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-499843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c112 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-92243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4871747/10000000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 98
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t112 : ((-10896666127/312500000000 : ℚ) : ℝ) ≤ stT130 112 := by
  have hc : ((-184511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10896666127/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-184511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c113 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((701619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -991411/5000000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 98
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t113 : ((8249749871/125000000000 : ℚ) : ℝ) ≤ stT130 113 := by
  have hc : ((701569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8249749871/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((701569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c114 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((938599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 880623/10000000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 98
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t114 : ((175806183033/2000000000000 : ℚ) : ℝ) ≤ stT130 114 := by
  have hc : ((938549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175806183033/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((938549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c115 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((8307/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 929769/2500000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 98
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t115 : ((483853013/62500000000 : ℚ) : ℝ) ≤ stT130 115 := by
  have hc : ((4151/50000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483853013/62500000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((4151/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c116 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-215901/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3266463/5000000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 98
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t116 : ((-400941437479/5000000000000 : ℚ) : ℝ) ≤ stT130 116 := by
  have hc : ((-431827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400941437479/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-431827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c117 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-166469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3192651/5000000) (δ := 1653/250000000) (ψ := -398611/1000000) 130 99
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t117 : ((-153910001979/2000000000000 : ℚ) : ℝ) ≤ stT130 117 := by
  have hc : ((-166479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153910001979/2000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-166479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c118 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((30689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144773/400000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 99
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t118 : ((28239988311/2500000000000 : ℚ) : ℝ) ≤ stT130 118 := by
  have hc : ((61353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28239988311/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((61353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c119 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((939137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175343/2000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 99
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t119 : ((430429587363/5000000000000 : ℚ) : ℝ) ≤ stT130 119 := by
  have hc : ((939087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430429587363/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((939087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c120 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((370179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1842983/10000000) (δ := 1653/250000000) (ψ := -398611/1000000) 130 99
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t120 : ((16895124099/250000000000 : ℚ) : ℝ) ≤ stT130 120 := by
  have hc : ((185077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16895124099/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((185077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c121 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-24279/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4540093/10000000) (δ := 1653/250000000) (ψ := -398611/1000000) 130 99
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t121 : ((-5519091461/250000000000 : ℚ) : ℝ) ≤ stT130 121 := by
  have hc : ((-6071/25000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5519091461/250000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-6071/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c122 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-483757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1443001/2000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 99
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t122 : ((-109498975989/1250000000000 : ℚ) : ℝ) ≤ stT130 122 := by
  have hc : ((-241891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109498975989/1250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-241891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c123 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-692651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2919943/5000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 100
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t123 : ((-62458771067/1000000000000 : ℚ) : ℝ) ≤ stT130 123 := by
  have hc : ((-692701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62458771067/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-692701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c124 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((56707/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401037/1250000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 100
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t124 : ((25457690061/1000000000000 : ℚ) : ℝ) ≤ stT130 124 := by
  have hc : ((56697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25457690061/1000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((56697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c125 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((121443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -597831/10000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 100
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t125 : ((434465231969/5000000000000 : ℚ) : ℝ) ≤ stT130 125 := by
  have hc : ((485747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434465231969/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((485747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c126 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((349523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995917/5000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 100
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t126 : ((15567864163/250000000000 : ℚ) : ℝ) ≤ stT130 126 := by
  have hc : ((174749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15567864163/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((174749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c127 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-250891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142531/312500) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 100
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t127 : ((-222674252937/10000000000000 : ℚ) : ℝ) ≤ stT130 127 := by
  have hc : ((-250941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222674252937/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-250941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c128 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-956049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 444377/625000) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 100
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t128 : ((-211270152129/2500000000000 : ℚ) : ℝ) ≤ stT130 128 := by
  have hc : ((-956099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211270152129/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-956099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c129 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-755679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1517179/2500000) (δ := 6627/1000000000) (ψ := -398611/1000000) 130 101
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t129 : ((-665382353779/10000000000000 : ℚ) : ℝ) ≤ stT130 129 := by
  have hc : ((-755729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-665382353779/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-755729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c130 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((146639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1779533/5000000) (δ := 6627/1000000000) (ψ := -398611/1000000) 130 101
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t130 : ((64283527581/5000000000000 : ℚ) : ℝ) ≤ stT130 130 := by
  have hc : ((146589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64283527581/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((146589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c131 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((455013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66789/625000) (δ := 411/62500000) (ψ := -398611/1000000) 130 101
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t131 : ((12422651111/156250000000 : ℚ) : ℝ) ≤ stT130 131 := by
  have hc : ((113747/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12422651111/156250000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((113747/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c132 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((169329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1402871/10000000) (δ := 411/62500000) (ψ := -398611/1000000) 130 101
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t132 : ((36843306443/500000000000 : ℚ) : ℝ) ≤ stT130 132 := by
  have hc : ((169319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36843306443/500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((169319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c133 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((7127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3855711/10000000) (δ := 411/62500000) (ψ := -398611/1000000) 130 101
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t133 : ((12338093961/5000000000000 : ℚ) : ℝ) ≤ stT130 133 := by
  have hc : ((14229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12338093961/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((14229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c134 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-810657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1572543/2500000) (δ := 1647/125000000) (ψ := -398611/1000000) 130 101
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t134 : ((-700344645383/10000000000000 : ℚ) : ℝ) ≤ stT130 134 := by
  have hc : ((-810707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-700344645383/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-810707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c135 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-471207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -875179/1250000) (δ := 3267/500000000) (ψ := -398611/1000000) 130 102
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t135 : ((-6337061669/78125000000 : ℚ) : ℝ) ≤ stT130 135 := by
  have hc : ((-14726/15625 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6337061669/78125000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-14726/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c136 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-133541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46029/100000) (δ := 6669/1000000000) (ψ := -398611/1000000) 130 102
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t136 : ((-57265955019/2500000000000 : ℚ) : ℝ) ≤ stT130 136 := by
  have hc : ((-66783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57265955019/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-66783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c137 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((63037/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2221917/10000000) (δ := 3267/500000000) (ψ := -398611/1000000) 130 102
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t137 : ((6731478803/125000000000 : ℚ) : ℝ) ≤ stT130 137 := by
  have hc : ((7879/12500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6731478803/125000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((7879/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c138 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((499197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14171/1000000) (δ := 6669/1000000000) (ψ := -398611/1000000) 130 102
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t138 : ((13278848751/156250000000 : ℚ) : ℝ) ≤ stT130 138 := by
  have hc : ((124793/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13278848751/156250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((124793/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c139 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((68029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622077/2500000) (δ := 3267/500000000) (ψ := -398611/1000000) 130 102
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t139 : ((57696080277/1250000000000 : ℚ) : ℝ) ≤ stT130 139 := by
  have hc : ((272091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57696080277/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((272091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c140 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-87233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481807/1000000) (δ := 6669/1000000000) (ψ := -398611/1000000) 130 102
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t140 : ((-29494388221/1000000000000 : ℚ) : ℝ) ≤ stT130 140 := by
  have hc : ((-174491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29494388221/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-174491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c141 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-1917/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285249/400000) (δ := 6669/1000000000) (ψ := -398611/1000000) 130 102
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t141 : ((-2018111999/25000000000 : ℚ) : ℝ) ≤ stT130 141 := by
  have hc : ((-19171/20000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2018111999/25000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-19171/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c142 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-808243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3139949/5000000) (δ := 3281/500000000) (ψ := -398611/1000000) 130 103
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t142 : ((-339152468163/5000000000000 : ℚ) : ℝ) ≤ stT130 142 := by
  have hc : ((-808293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339152468163/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-808293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c143 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-28871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1999589/5000000) (δ := 3281/500000000) (ψ := -398611/1000000) 130 103
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t143 : ((-24184983803/10000000000000 : ℚ) : ℝ) ≤ stT130 143 := by
  have hc : ((-28921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24184983803/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-28921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c144 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((192213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1734383/10000000) (δ := 3281/500000000) (ψ := -398611/1000000) 130 103
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t144 : ((320334038533/5000000000000 : ℚ) : ℝ) ≤ stT130 144 := by
  have hc : ((384401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320334038533/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((384401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c145 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((7831/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25739/500000) (δ := 6641/1000000000) (ψ := -398611/1000000) 130 103
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t145 : ((16257382731/200000000000 : ℚ) : ℝ) ≤ stT130 145 := by
  have hc : ((39153/40000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16257382731/200000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((39153/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c146 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((454141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343559/1250000) (δ := 3281/500000000) (ψ := -398611/1000000) 130 103
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t146 : ((75161596411/2000000000000 : ℚ) : ℝ) ≤ stT130 146 := by
  have hc : ((454091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75161596411/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((454091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c147 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-101017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 496689/1000000) (δ := 6641/1000000000) (ψ := -398611/1000000) 130 103
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t147 : ((-166655636433/5000000000000 : ℚ) : ℝ) ≤ stT130 147 := by
  have hc : ((-202059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166655636433/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-202059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c148 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-481419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1792573/2500000) (δ := 3281/500000000) (ψ := -398611/1000000) 130 103
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t148 : ((-19787228039/250000000000 : ℚ) : ℝ) ≤ stT130 148 := by
  have hc : ((-120361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19787228039/250000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-120361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c149 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-824229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6349089/10000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 104
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t149 : ((-21102366679/312500000000 : ℚ) : ℝ) ≤ stT130 149 := by
  have hc : ((-824279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21102366679/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-824279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c150 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-99119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1043799/2500000) (δ := 1637/250000000) (ψ := -398611/1000000) 130 104
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t150 : ((-80971190993/10000000000000 : ℚ) : ℝ) ≤ stT130 150 := by
  have hc : ((-99169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80971190993/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-99169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c151 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((173047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2015701/10000000) (δ := 1637/250000000) (ψ := -398611/1000000) 130 104
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t151 : ((70406699843/1250000000000 : ℚ) : ℝ) ≤ stT130 151 := by
  have hc : ((346069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70406699843/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((346069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c152 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((499329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64763/5000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 104
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t152 : ((50623621191/625000000000 : ℚ) : ℝ) ≤ stT130 152 := by
  have hc : ((62413/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50623621191/625000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((62413/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c153 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((309129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2260681/10000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 104
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t153 : ((3904621047/78125000000 : ℚ) : ℝ) ≤ stT130 153 := by
  have hc : ((19319/31250 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3904621047/78125000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((19319/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c154 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-179411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4377959/10000000) (δ := 1637/250000000) (ψ := -398611/1000000) 130 104
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t154 : ((-144613801403/10000000000000 : ℚ) : ℝ) ≤ stT130 154 := by
  have hc : ((-179461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144613801403/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-179461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c155 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-170611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6481521/10000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 104
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t155 : ((-6852309981/100000000000 : ℚ) : ℝ) ≤ stT130 155 := by
  have hc : ((-170621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6852309981/100000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-170621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c156 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-59943/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7136399/10000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 105
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t156 : ((-383962603729/5000000000000 : ℚ) : ℝ) ≤ stT130 156 := by
  have hc : ((-479569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383962603729/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-479569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c157 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-87549/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2529857/5000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 105
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t157 : ((-69879699633/2000000000000 : ℚ) : ℝ) ≤ stT130 157 := by
  have hc : ((-87559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69879699633/2000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-87559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c158 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((72753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23408/78125) (δ := 1331/200000000) (ψ := -398611/1000000) 130 105
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t158 : ((57871202851/2000000000000 : ℚ) : ℝ) ≤ stT130 158 := by
  have hc : ((72743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57871202851/2000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((72743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c159 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((58081/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -472867/5000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 105
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t159 : ((368469734773/5000000000000 : ℚ) : ℝ) ≤ stT130 159 := by
  have hc : ((464623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368469734773/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((464623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c160 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((906129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545943/5000000) (δ := 1331/200000000) (ψ := -398611/1000000) 130 105
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t160 : ((716317968951/10000000000000 : ℚ) : ℝ) ≤ stT130 160 := by
  have hc : ((906079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((716317968951/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((906079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c161 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((159217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1558399/5000000) (δ := 1637/250000000) (ψ := -398611/1000000) 130 105
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t161 : ((1568260089/62500000000 : ℚ) : ℝ) ≤ stT130 161 := by
  have hc : ((19899/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1568260089/62500000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((19899/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c162 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-231281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2564599/5000000) (δ := 1637/250000000) (ψ := -398611/1000000) 130 105
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t162 : ((-3634626831/100000000000 : ℚ) : ℝ) ≤ stT130 162 := by
  have hc : ((-115653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3634626831/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-115653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c163 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-958271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55697/78125) (δ := 1331/200000000) (ψ := -398611/1000000) 130 105
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t163 : ((-750615464781/10000000000000 : ℚ) : ℝ) ≤ stT130 163 := by
  have hc : ((-958321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750615464781/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-958321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c164 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-437539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6590983/10000000) (δ := 83/12500000) (ψ := -398611/1000000) 130 106
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t164 : ((-85420040779/1250000000000 : ℚ) : ℝ) ≤ stT130 164 := by
  have hc : ((-109391/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85420040779/1250000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-109391/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c165 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-135931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153827/2500000) (δ := 83/12500000) (ψ := -398611/1000000) 130 106
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t165 : ((-26460402511/1250000000000 : ℚ) : ℝ) ≤ stT130 165 := by
  have hc : ((-33989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26460402511/1250000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-33989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c166 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((61041/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66289/250000) (δ := 6563/1000000000) (ψ := -398611/1000000) 130 106
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t166 : ((3789769697/100000000000 : ℚ) : ℝ) ≤ stT130 166 := by
  have hc : ((244139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3789769697/100000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((244139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c167 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((480551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349789/5000000) (δ := 83/12500000) (ψ := -398611/1000000) 130 106
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t167 : ((185921035449/2500000000000 : ℚ) : ℝ) ≤ stT130 167 := by
  have hc : ((240263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185921035449/2500000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((240263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c168 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((879359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248141/2000000) (δ := 6563/1000000000) (ψ := -398611/1000000) 130 106
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t168 : ((169600240611/2500000000000 : ℚ) : ℝ) ≤ stT130 168 := by
  have hc : ((879309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169600240611/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((879309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c169 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((37297/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 633903/2000000) (δ := 6563/1000000000) (ψ := -398611/1000000) 130 106
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t169 : ((11474065449/500000000000 : ℚ) : ℝ) ≤ stT130 169 := by
  have hc : ((149163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11474065449/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((149163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c170 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-223751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5086917/10000000) (δ := 83/12500000) (ψ := -398611/1000000) 130 106
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t170 : ((-1072677249/31250000000 : ℚ) : ℝ) ≤ stT130 170 := by
  have hc : ((-6993/15625 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1072677249/31250000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-6993/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c171 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-941291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279723/400000) (δ := 6563/1000000000) (ψ := -398611/1000000) 130 106
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t171 : ((-8998278619/125000000000 : ℚ) : ℝ) ≤ stT130 171 := by
  have hc : ((-941341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8998278619/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-941341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c172 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-457829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3409923/5000000) (δ := 6533/1000000000) (ψ := -398611/1000000) 130 107
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t172 : ((-174555235011/2500000000000 : ℚ) : ℝ) ≤ stT130 172 := by
  have hc : ((-228927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174555235011/2500000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-228927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c173 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-392657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1233947/2500000) (δ := 667/100000000) (ψ := -398611/1000000) 130 107
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t173 : ((-149284817101/5000000000000 : ℚ) : ℝ) ≤ stT130 173 := by
  have hc : ((-392707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149284817101/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-392707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c174 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((169457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1531293/5000000) (δ := 6533/1000000000) (ψ := -398611/1000000) 130 107
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t174 : ((8027878771/312500000000 : ℚ) : ℝ) ≤ stT130 174 := by
  have hc : ((21179/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8027878771/312500000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((21179/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c175 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((35479/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -300027/2500000) (δ := 667/100000000) (ψ := -398611/1000000) 130 107
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t175 : ((3352257207/50000000000 : ℚ) : ℝ) ≤ stT130 175 := by
  have hc : ((35477/40000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3352257207/50000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((35477/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c176 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((966211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325871/5000000) (δ := 667/100000000) (ψ := -398611/1000000) 130 107
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t176 : ((364135453129/5000000000000 : ℚ) : ℝ) ≤ stT130 176 := by
  have hc : ((966161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364135453129/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((966161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c177 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((271307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2493127/10000000) (δ := 667/100000000) (ψ := -398611/1000000) 130 107
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t177 : ((50977007543/1250000000000 : ℚ) : ℝ) ≤ stT130 177 := by
  have hc : ((135641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50977007543/1250000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((135641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c178 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-158181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270257/625000) (δ := 667/100000000) (ψ := -398611/1000000) 130 107
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t178 : ((-29649799473/2500000000000 : ℚ) : ℝ) ≤ stT130 178 := by
  have hc : ((-158231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29649799473/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-158231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c179 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-775273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6144859/10000000) (δ := 6533/1000000000) (ψ := -398611/1000000) 130 107
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t179 : ((-144876080457/2500000000000 : ℚ) : ℝ) ≤ stT130 179 := by
  have hc : ((-775323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144876080457/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-775323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c180 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-999177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7752529/10000000) (δ := 6577/1000000000) (ψ := -398611/1000000) 130 108
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t180 : ((-186194959953/2500000000000 : ℚ) : ℝ) ≤ stT130 180 := by
  have hc : ((-999227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186194959953/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-999227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c181 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-18107/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1487991/2500000) (δ := 6577/1000000000) (ψ := -398611/1000000) 130 108
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t181 : ((-10767817347/200000000000 : ℚ) : ℝ) ≤ stT130 181 := by
  have hc : ((-72433/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10767817347/200000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-72433/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c182 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-23401/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65021/156250) (δ := 6577/1000000000) (ψ := -398611/1000000) 130 108
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t182 : ((-27768411/4000000000 : ℚ) : ℝ) ≤ stT130 182 := by
  have hc : ((-46827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27768411/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-46827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c183 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((57989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2380507/10000000) (δ := 3313/500000000) (ψ := -398611/1000000) 130 108
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t183 : ((334867113/7812500000 : ℚ) : ℝ) ≤ stT130 183 := by
  have hc : ((1812/3125 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334867113/7812500000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((1812/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c184 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((970439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -609387/10000000) (δ := 3313/500000000) (ψ := -398611/1000000) 130 108
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t184 : ((715379504301/10000000000000 : ℚ) : ℝ) ≤ stT130 184 := by
  have hc : ((970389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((715379504301/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((970389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c185 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((895671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 576073/5000000) (δ := 6577/1000000000) (ψ := -398611/1000000) 130 108
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t185 : ((329236548947/5000000000000 : ℚ) : ℝ) ≤ stT130 185 := by
  have hc : ((895621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329236548947/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((895621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c186 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((79563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 726039/2500000) (δ := 6577/1000000000) (ψ := -398611/1000000) 130 108
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t186 : ((11666208791/400000000000 : ℚ) : ℝ) ≤ stT130 186 := by
  have hc : ((79553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11666208791/400000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((79553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c187 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-70991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2323403/5000000) (δ := 6577/1000000000) (ψ := -398611/1000000) 130 108
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t187 : ((-103845884911/5000000000000 : ℚ) : ℝ) ≤ stT130 187 := by
  have hc : ((-142007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103845884911/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-142007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c188 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-207799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199379/312500) (δ := 3313/500000000) (ψ := -398611/1000000) 130 108
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t188 : ((-12124969779/200000000000 : ℚ) : ℝ) ≤ stT130 188 := by
  have hc : ((-415623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12124969779/200000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-415623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c189 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-62187/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7603677/10000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 109
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t189 : ((-361893292753/5000000000000 : ℚ) : ℝ) ≤ stT130 189 := by
  have hc : ((-497521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361893292753/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-497521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c190 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-176647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1472163/2500000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 109
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t190 : ((-256324808163/5000000000000 : ℚ) : ℝ) ≤ stT130 190 := by
  have hc : ((-353319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256324808163/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-353319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c191 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-6379/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4182597/10000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 109
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t191 : ((-1477742751/200000000000 : ℚ) : ℝ) ≤ stT130 191 := by
  have hc : ((-51057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1477742751/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-51057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c192 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((27259/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62137/250000) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 109
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t192 : ((39341323431/1000000000000 : ℚ) : ℝ) ≤ stT130 192 := by
  have hc : ((54513/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39341323431/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((54513/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c193 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((949591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79717/1000000) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 109
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t193 : ((136698770983/2000000000000 : ℚ) : ℝ) ≤ stT130 193 := by
  have hc : ((949541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136698770983/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((949541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c194 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((938349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88243/1000000) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 109
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t194 : ((336829636721/5000000000000 : ℚ) : ℝ) ≤ stT130 194 := by
  have hc : ((938299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336829636721/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((938299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c195 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((130553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 510677/2000000) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 109
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t195 : ((93481879617/2500000000000 : ℚ) : ℝ) ≤ stT130 195 := by
  have hc : ((261081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93481879617/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((261081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c196 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-1801/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4215793/10000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 109
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t196 : ((-20591793951/2500000000000 : ℚ) : ℝ) ≤ stT130 196 := by
  have hc : ((-57657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20591793951/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-57657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c197 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-701217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23479/40000) (δ := 6519/1000000000) (ψ := -398611/1000000) 130 109
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t197 : ((-499632400757/10000000000000 : ℚ) : ℝ) ≤ stT130 197 := by
  have hc : ((-701267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499632400757/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-701267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c198 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-990839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7515323/10000000) (δ := 1671/250000000) (ψ := -398611/1000000) 130 109
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t198 : ((-70419508563/1000000000000 : ℚ) : ℝ) ≤ stT130 198 := by
  have hc : ((-990889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70419508563/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-990889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c199 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-217023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1638839/2500000) (δ := 1653/250000000) (ψ := -398611/1000000) 130 110
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t199 : ((-153852559311/2500000000000 : ℚ) : ℝ) ≤ stT130 199 := by
  have hc : ((-434071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153852559311/2500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-434071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c200 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-389161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4926293/10000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t200 : ((-275213822577/10000000000000 : ℚ) : ℝ) ≤ stT130 200 := by
  have hc : ((-389211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275213822577/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-389211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c201 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((7691/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305323/10000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t201 : ((17355860139/1000000000000 : ℚ) : ℝ) ≤ stT130 201 := by
  have hc : ((123031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17355860139/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((123031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c202 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((779469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -846223/5000000) (δ := 1653/250000000) (ψ := -398611/1000000) 130 110
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t202 : ((548396870143/10000000000000 : ℚ) : ℝ) ≤ stT130 202 := by
  have hc : ((779419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548396870143/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((779419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c203 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((249847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43749/5000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t203 : ((175349341839/2500000000000 : ℚ) : ℝ) ≤ stT130 203 := by
  have hc : ((499669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175349341839/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((499669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c204 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((205793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94347/625000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t204 : ((14407515927/250000000000 : ℚ) : ℝ) ≤ stT130 204 := by
  have hc : ((411561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14407515927/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((411561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c205 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((325249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1549401/5000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t205 : ((22712873757/1000000000000 : ℚ) : ℝ) ≤ stT130 205 := by
  have hc : ((325199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22712873757/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((325199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c206 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-296791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4680317/10000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t206 : ((-103409608647/5000000000000 : ℚ) : ℝ) ≤ stT130 206 := by
  have hc : ((-296841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103409608647/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-296841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c207 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-802139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3127081/5000000) (δ := 6591/1000000000) (ψ := -398611/1000000) 130 110
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t207 : ((-557560662261/10000000000000 : ℚ) : ℝ) ≤ stT130 207 := by
  have hc : ((-802189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557560662261/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-802189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c208 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-99991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3910217/5000000) (δ := 1653/250000000) (ψ := -398611/1000000) 130 110
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t208 : ((-135419583/1953125000 : ℚ) : ℝ) ≤ stT130 208 := by
  have hc : ((-24999/25000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135419583/1953125000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-24999/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c209 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-409799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1582191/2500000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 111
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t209 : ((-1771758801/31250000000 : ℚ) : ℝ) ≤ stT130 209 := by
  have hc : ((-12807/15625 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1771758801/31250000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-12807/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c210 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-333657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4777441/10000000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 111
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t210 : ((-115139927331/5000000000000 : ℚ) : ℝ) ≤ stT130 210 := by
  have hc : ((-333707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115139927331/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-333707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c211 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((136927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404187/1250000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 111
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t211 : ((11780896257/625000000000 : ℚ) : ℝ) ≤ stT130 211 := by
  have hc : ((68451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11780896257/625000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((68451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c212 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((778361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53027/312500) (δ := 1301/200000000) (ψ := -398611/1000000) 130 111
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t212 : ((267272775711/5000000000000 : ℚ) : ℝ) ≤ stT130 212 := by
  have hc : ((778311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267272775711/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((778311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c213 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((498879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83723/5000000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 111
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t213 : ((42726096819/625000000000 : ℚ) : ℝ) ≤ stT130 213 := by
  have hc : ((249427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42726096819/625000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((249427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c214 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((214179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1354821/10000000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 111
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t214 : ((58560402761/1000000000000 : ℚ) : ℝ) ≤ stT130 214 := by
  have hc : ((428333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58560402761/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((428333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c215 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((410323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2869971/10000000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 111
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t215 : ((139901862181/5000000000000 : ℚ) : ℝ) ≤ stT130 215 := by
  have hc : ((410273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139901862181/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((410273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c216 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-89733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4378101/10000000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 111
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t216 : ((-15268149953/1250000000000 : ℚ) : ℝ) ≤ stT130 216 := by
  have hc : ((-44879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15268149953/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-44879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c217 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-8799/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1469811/2500000) (δ := 3349/500000000) (ψ := -398611/1000000) 130 111
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t217 : ((-9557730293/200000000000 : ℚ) : ℝ) ≤ stT130 217 := by
  have hc : ((-70397/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9557730293/200000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-70397/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c218 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-981587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 921687/1250000) (δ := 1301/200000000) (ψ := -398611/1000000) 130 111
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t218 : ((-332424498591/5000000000000 : ℚ) : ℝ) ≤ stT130 218 := by
  have hc : ((-981637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332424498591/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-981637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c219 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-114997/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21397/31250) (δ := 6597/1000000000) (ψ := -398611/1000000) 130 112
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t219 : ((-155424132297/2500000000000 : ℚ) : ℝ) ≤ stT130 219 := by
  have hc : ((-460013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155424132297/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-460013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c220 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-544477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073281/2000000) (δ := 6597/1000000000) (ψ := -398611/1000000) 130 112
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t220 : ((-1835600517/50000000000 : ℚ) : ℝ) ≤ stT130 220 := by
  have hc : ((-544527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1835600517/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-544527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c221 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((1381/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -778493/2000000) (δ := 6597/1000000000) (ψ := -398611/1000000) 130 112
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t221 : ((903903/976562500 : ℚ) : ℝ) ≤ stT130 221 := by
  have hc : ((43/3125 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((903903/976562500 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((43/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c222 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((565227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121261/500000) (δ := 6597/1000000000) (ψ := -398611/1000000) 130 112
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t222 : ((94830483653/2500000000000 : ℚ) : ℝ) ≤ stT130 222 := by
  have hc : ((565177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94830483653/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((565177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c223 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((231623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48227/500000) (δ := 6597/1000000000) (ψ := -398611/1000000) 130 112
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t223 : ((310195479429/5000000000000 : ℚ) : ℝ) ≤ stT130 223 := by
  have hc : ((463221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310195479429/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((463221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c224 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((245221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61201/1250000) (δ := 3303/500000000) (ψ := -398611/1000000) 130 112
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t224 : ((327673589801/5000000000000 : ℚ) : ℝ) ≤ stT130 224 := by
  have hc : ((490417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327673589801/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((490417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c225 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((8931/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242161/1250000) (δ := 3303/500000000) (ψ := -398611/1000000) 130 112
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t225 : ((23814309519/500000000000 : ℚ) : ℝ) ≤ stT130 225 := by
  have hc : ((71443/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23814309519/500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((71443/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c226 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((108817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 844629/2500000) (δ := 13197/1000000000) (ψ := -398611/1000000) 130 112
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t226 : ((904591881/62500000000 : ℚ) : ℝ) ≤ stT130 226 := by
  have hc : ((13599/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904591881/62500000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((13599/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c227 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-21699/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150419/312500) (δ := 3303/500000000) (ψ := -398611/1000000) 130 112
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t227 : ((-28808442427/1250000000000 : ℚ) : ℝ) ≤ stT130 227 := by
  have hc : ((-173617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28808442427/1250000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-173617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c228 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-799219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3120989/5000000) (δ := 3303/500000000) (ψ := -398611/1000000) 130 112
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t228 : ((-529329482823/10000000000000 : ℚ) : ℝ) ≤ stT130 228 := by
  have hc : ((-799269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529329482823/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-799269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c229 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-997123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1916077/2500000) (δ := 3303/500000000) (ψ := -398611/1000000) 130 112
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t229 : ((-658950864687/10000000000000 : ℚ) : ℝ) ≤ stT130 229 := by
  have hc : ((-997173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658950864687/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-997173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c230 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-44103/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6627533/10000000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t230 : ((-58164657391/1000000000000 : ℚ) : ℝ) ≤ stT130 230 := by
  have hc : ((-88211/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58164657391/1000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-88211/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c231 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-617/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5217553/10000000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t231 : ((-202998753/6250000000 : ℚ) : ℝ) ≤ stT130 231 := by
  have hc : ((-9873/20000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202998753/6250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-9873/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c232 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((11327/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3813683/10000000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t232 : ((3714165657/1250000000000 : ℚ) : ℝ) ≤ stT130 232 := by
  have hc : ((22629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3714165657/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((22629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c233 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((568323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1207913/5000000) (δ := 669/100000000) (ψ := -398611/1000000) 130 113
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t233 : ((372287576033/10000000000000 : ℚ) : ℝ) ≤ stT130 233 := by
  have hc : ((568273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372287576033/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((568273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c234 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((114661/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -255987/2500000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t234 : ((7495210317/125000000000 : ℚ) : ℝ) ≤ stT130 234 := by
  have hc : ((458619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7495210317/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((458619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c235 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((30923/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180991/5000000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t235 : ((40341838963/625000000000 : ℚ) : ℝ) ≤ stT130 235 := by
  have hc : ((494743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40341838963/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((494743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c236 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((191723/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1742029/10000000) (δ := 669/100000000) (ψ := -398611/1000000) 130 113
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t236 : ((3899774991/78125000000 : ℚ) : ℝ) ≤ stT130 236 := by
  have hc : ((383421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3899774991/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((383421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c237 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((318651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3116227/10000000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t237 : ((206953332969/10000000000000 : ℚ) : ℝ) ≤ stT130 237 := by
  have hc : ((318601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206953332969/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((318601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c238 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-110607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4484639/10000000) (δ := 669/100000000) (ψ := -398611/1000000) 130 113
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t238 : ((-2241003279/156250000000 : ℚ) : ℝ) ≤ stT130 238 := by
  have hc : ((-13829/62500 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2241003279/156250000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-13829/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c239 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-173699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1461833/2500000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t239 : ((-224729525281/5000000000000 : ℚ) : ℝ) ≤ stT130 239 := by
  have hc : ((-347423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224729525281/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-347423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c240 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-966427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7204337/10000000) (δ := 6513/1000000000) (ψ := -398611/1000000) 130 113
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t240 : ((-311929485273/5000000000000 : ℚ) : ℝ) ≤ stT130 240 := by
  have hc : ((-966477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311929485273/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-966477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c241 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-960867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1788069/2500000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t241 : ((-618981411969/10000000000000 : ℚ) : ℝ) ≤ stT130 241 := by
  have hc : ((-960917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618981411969/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-960917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c242 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-341481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1451629/2500000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t242 : ((-4390571889/100000000000 : ℚ) : ℝ) ≤ stT130 242 := by
  have hc : ((-170753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4390571889/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-170753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c243 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-10703/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2233157/5000000) (δ := 6583/1000000000) (ψ := -398611/1000000) 130 114
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t243 : ((-13735177911/1000000000000 : ℚ) : ℝ) ≤ stT130 243 := by
  have hc : ((-21411/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13735177911/1000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-21411/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c244 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((156407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782901/2500000) (δ := 6583/1000000000) (ψ := -398611/1000000) 130 114
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t244 : ((6257078393/312500000000 : ℚ) : ℝ) ≤ stT130 244 := by
  have hc : ((78191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6257078393/312500000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((78191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c245 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((37559/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180237/1000000) (δ := 651/50000000) (ψ := -398611/1000000) 130 114
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t245 : ((11996973247/250000000000 : ℚ) : ℝ) ≤ stT130 245 := by
  have hc : ((75113/100000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11996973247/250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((75113/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c246 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((981737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478531/10000000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t246 : ((78237508839/1250000000000 : ℚ) : ℝ) ≤ stT130 246 := by
  have hc : ((981687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78237508839/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((981687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c247 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((94409/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 839929/10000000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t247 : ((3754234671/62500000000 : ℚ) : ℝ) ≤ stT130 247 := by
  have hc : ((23601/25000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3754234671/62500000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((23601/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c248 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((65151/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2153059/10000000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t248 : ((4136771/100000000 : ℚ) : ℝ) ≤ stT130 248 := by
  have hc : ((32573/50000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4136771/100000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((32573/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c249 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((92681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3460891/10000000) (δ := 6583/1000000000) (ψ := -398611/1000000) 130 114
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t249 : ((917473921/78125000000 : ℚ) : ℝ) ≤ stT130 249 := by
  have hc : ((5791/31250 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((917473921/78125000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((5791/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_c250 :
    |Real.cos (((130 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((-82101/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1190881/2500000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st130_t250 : ((-12983293939/625000000000 : ℚ) : ℝ) ≤ stT130 250 := by
  have hc : ((-164227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((130 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st130_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12983293939/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-164227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st130_p1 : ((921551/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT130 (i+1) := by
  rw [Finset.sum_range_one]
  exact st130_t1

theorem st130_p2 : ((421619401523/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT130 (i+1))
      = (∑ i ∈ Finset.range 1, stT130 (i+1)) + stT130 2 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 1
    simpa using h
  have hprev := st130_p1
  have hstep := st130_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p3 : ((2472271435549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT130 (i+1))
      = (∑ i ∈ Finset.range 2, stT130 (i+1)) + stT130 3 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 2
    simpa using h
  have hprev := st130_p2
  have hstep := st130_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p4 : ((4820797846349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT130 (i+1))
      = (∑ i ∈ Finset.range 3, stT130 (i+1)) + stT130 4 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 3
    simpa using h
  have hprev := st130_p3
  have hstep := st130_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p5 : ((1906731668069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT130 (i+1))
      = (∑ i ∈ Finset.range 4, stT130 (i+1)) + stT130 5 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 4
    simpa using h
  have hprev := st130_p4
  have hstep := st130_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p6 : ((4602480264791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT130 (i+1))
      = (∑ i ∈ Finset.range 5, stT130 (i+1)) + stT130 6 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 5
    simpa using h
  have hprev := st130_p5
  have hstep := st130_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p7 : ((1447423996363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT130 (i+1))
      = (∑ i ∈ Finset.range 6, stT130 (i+1)) + stT130 7 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 6
    simpa using h
  have hprev := st130_p6
  have hstep := st130_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p8 : ((1477641429467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT130 (i+1))
      = (∑ i ∈ Finset.range 7, stT130 (i+1)) + stT130 8 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 7
    simpa using h
  have hprev := st130_p7
  have hstep := st130_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p9 : ((653984598069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT130 (i+1))
      = (∑ i ∈ Finset.range 8, stT130 (i+1)) + stT130 9 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 8
    simpa using h
  have hprev := st130_p8
  have hstep := st130_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p10 : ((859654625217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT130 (i+1))
      = (∑ i ∈ Finset.range 9, stT130 (i+1)) + stT130 10 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 9
    simpa using h
  have hprev := st130_p9
  have hstep := st130_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p11 : ((185610814947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT130 (i+1))
      = (∑ i ∈ Finset.range 10, stT130 (i+1)) + stT130 11 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 10
    simpa using h
  have hprev := st130_p10
  have hstep := st130_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p12 : ((-248430148697/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT130 (i+1))
      = (∑ i ∈ Finset.range 11, stT130 (i+1)) + stT130 12 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 11
    simpa using h
  have hprev := st130_p11
  have hstep := st130_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p13 : ((-61924199747/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT130 (i+1))
      = (∑ i ∈ Finset.range 12, stT130 (i+1)) + stT130 13 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 12
    simpa using h
  have hprev := st130_p12
  have hstep := st130_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p14 : ((-1966615787903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT130 (i+1))
      = (∑ i ∈ Finset.range 13, stT130 (i+1)) + stT130 14 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 13
    simpa using h
  have hprev := st130_p13
  have hstep := st130_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p15 : ((183366889877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT130 (i+1))
      = (∑ i ∈ Finset.range 14, stT130 (i+1)) + stT130 15 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 14
    simpa using h
  have hprev := st130_p14
  have hstep := st130_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p16 : ((-414007802297/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT130 (i+1))
      = (∑ i ∈ Finset.range 15, stT130 (i+1)) + stT130 16 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 15
    simpa using h
  have hprev := st130_p15
  have hstep := st130_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p17 : ((-3060874957409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT130 (i+1))
      = (∑ i ∈ Finset.range 16, stT130 (i+1)) + stT130 17 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 16
    simpa using h
  have hprev := st130_p16
  have hstep := st130_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p18 : ((-1495119384941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT130 (i+1))
      = (∑ i ∈ Finset.range 17, stT130 (i+1)) + stT130 18 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 17
    simpa using h
  have hprev := st130_p17
  have hstep := st130_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p19 : ((787773304189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT130 (i+1))
      = (∑ i ∈ Finset.range 18, stT130 (i+1)) + stT130 19 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 18
    simpa using h
  have hprev := st130_p18
  have hstep := st130_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p20 : ((366587556167/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT130 (i+1))
      = (∑ i ∈ Finset.range 19, stT130 (i+1)) + stT130 20 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 19
    simpa using h
  have hprev := st130_p19
  have hstep := st130_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p21 : ((623194231543/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT130 (i+1))
      = (∑ i ∈ Finset.range 20, stT130 (i+1)) + stT130 21 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 20
    simpa using h
  have hprev := st130_p20
  have hstep := st130_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p22 : ((1776126110369/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT130 (i+1))
      = (∑ i ∈ Finset.range 21, stT130 (i+1)) + stT130 22 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 21
    simpa using h
  have hprev := st130_p21
  have hstep := st130_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p23 : ((451481828803/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT130 (i+1))
      = (∑ i ∈ Finset.range 22, stT130 (i+1)) + stT130 23 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 22
    simpa using h
  have hprev := st130_p22
  have hstep := st130_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p24 : ((9873369254723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT130 (i+1))
      = (∑ i ∈ Finset.range 23, stT130 (i+1)) + stT130 24 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 23
    simpa using h
  have hprev := st130_p23
  have hstep := st130_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p25 : ((441382136593/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT130 (i+1))
      = (∑ i ∈ Finset.range 24, stT130 (i+1)) + stT130 25 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 24
    simpa using h
  have hprev := st130_p24
  have hstep := st130_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p26 : ((3446324258213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT130 (i+1))
      = (∑ i ∈ Finset.range 25, stT130 (i+1)) + stT130 26 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 25
    simpa using h
  have hprev := st130_p25
  have hstep := st130_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p27 : ((106794019709/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT130 (i+1))
      = (∑ i ∈ Finset.range 26, stT130 (i+1)) + stT130 27 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 26
    simpa using h
  have hprev := st130_p26
  have hstep := st130_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p28 : ((4361298181897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT130 (i+1))
      = (∑ i ∈ Finset.range 27, stT130 (i+1)) + stT130 28 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 27
    simpa using h
  have hprev := st130_p27
  have hstep := st130_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p29 : ((4263845235977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT130 (i+1))
      = (∑ i ∈ Finset.range 28, stT130 (i+1)) + stT130 29 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 28
    simpa using h
  have hprev := st130_p28
  have hstep := st130_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p30 : ((685339011937/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT130 (i+1))
      = (∑ i ∈ Finset.range 29, stT130 (i+1)) + stT130 30 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 29
    simpa using h
  have hprev := st130_p29
  have hstep := st130_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p31 : ((4107212357173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT130 (i+1))
      = (∑ i ∈ Finset.range 30, stT130 (i+1)) + stT130 31 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 30
    simpa using h
  have hprev := st130_p30
  have hstep := st130_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p32 : ((4218014162287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT130 (i+1))
      = (∑ i ∈ Finset.range 31, stT130 (i+1)) + stT130 32 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 31
    simpa using h
  have hprev := st130_p31
  have hstep := st130_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p33 : ((3492963134017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT130 (i+1))
      = (∑ i ∈ Finset.range 32, stT130 (i+1)) + stT130 33 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 32
    simpa using h
  have hprev := st130_p32
  have hstep := st130_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p34 : ((8680803068909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT130 (i+1))
      = (∑ i ∈ Finset.range 33, stT130 (i+1)) + stT130 34 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 33
    simpa using h
  have hprev := st130_p33
  have hstep := st130_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p35 : ((7478743204177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT130 (i+1))
      = (∑ i ∈ Finset.range 34, stT130 (i+1)) + stT130 35 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 34
    simpa using h
  have hprev := st130_p34
  have hstep := st130_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p36 : ((7923909692777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT130 (i+1))
      = (∑ i ∈ Finset.range 35, stT130 (i+1)) + stT130 36 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 35
    simpa using h
  have hprev := st130_p35
  have hstep := st130_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p37 : ((4084623551607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT130 (i+1))
      = (∑ i ∈ Finset.range 36, stT130 (i+1)) + stT130 37 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 36
    simpa using h
  have hprev := st130_p36
  have hstep := st130_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p38 : ((3713548359217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT130 (i+1))
      = (∑ i ∈ Finset.range 37, stT130 (i+1)) + stT130 38 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 37
    simpa using h
  have hprev := st130_p37
  have hstep := st130_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p39 : ((4235597990837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT130 (i+1))
      = (∑ i ∈ Finset.range 38, stT130 (i+1)) + stT130 39 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 38
    simpa using h
  have hprev := st130_p38
  have hstep := st130_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p40 : ((1454560343653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT130 (i+1))
      = (∑ i ∈ Finset.range 39, stT130 (i+1)) + stT130 40 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 39
    simpa using h
  have hprev := st130_p39
  have hstep := st130_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p41 : ((426162274537/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT130 (i+1))
      = (∑ i ∈ Finset.range 40, stT130 (i+1)) + stT130 41 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 40
    simpa using h
  have hprev := st130_p40
  have hstep := st130_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p42 : ((9119876021/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT130 (i+1))
      = (∑ i ∈ Finset.range 41, stT130 (i+1)) + stT130 42 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 41
    simpa using h
  have hprev := st130_p41
  have hstep := st130_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p43 : ((1685661480653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT130 (i+1))
      = (∑ i ∈ Finset.range 42, stT130 (i+1)) + stT130 43 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 42
    simpa using h
  have hprev := st130_p42
  have hstep := st130_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p44 : ((1495118336309/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT130 (i+1))
      = (∑ i ∈ Finset.range 43, stT130 (i+1)) + stT130 44 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 43
    simpa using h
  have hprev := st130_p43
  have hstep := st130_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p45 : ((508906343537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT130 (i+1))
      = (∑ i ∈ Finset.range 44, stT130 (i+1)) + stT130 45 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 44
    simpa using h
  have hprev := st130_p44
  have hstep := st130_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p46 : ((984889257079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT130 (i+1))
      = (∑ i ∈ Finset.range 45, stT130 (i+1)) + stT130 46 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 45
    simpa using h
  have hprev := st130_p45
  have hstep := st130_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p47 : ((477355988277/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT130 (i+1))
      = (∑ i ∈ Finset.range 46, stT130 (i+1)) + stT130 47 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 46
    simpa using h
  have hprev := st130_p46
  have hstep := st130_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p48 : ((8417575862307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT130 (i+1))
      = (∑ i ∈ Finset.range 47, stT130 (i+1)) + stT130 48 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 47
    simpa using h
  have hprev := st130_p47
  have hstep := st130_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p49 : ((7191343943243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT130 (i+1))
      = (∑ i ∈ Finset.range 48, stT130 (i+1)) + stT130 49 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 48
    simpa using h
  have hprev := st130_p48
  have hstep := st130_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p50 : ((8605093081379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT130 (i+1))
      = (∑ i ∈ Finset.range 49, stT130 (i+1)) + stT130 50 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 49
    simpa using h
  have hprev := st130_p49
  have hstep := st130_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p51 : ((3703315190533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT130 (i+1))
      = (∑ i ∈ Finset.range 50, stT130 (i+1)) + stT130 51 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 50
    simpa using h
  have hprev := st130_p50
  have hstep := st130_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p52 : ((1989801123329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT130 (i+1))
      = (∑ i ∈ Finset.range 51, stT130 (i+1)) + stT130 52 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 51
    simpa using h
  have hprev := st130_p51
  have hstep := st130_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p53 : ((8306189478761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT130 (i+1))
      = (∑ i ∈ Finset.range 52, stT130 (i+1)) + stT130 53 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 52
    simpa using h
  have hprev := st130_p52
  have hstep := st130_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p54 : ((287434859913/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT130 (i+1))
      = (∑ i ∈ Finset.range 53, stT130 (i+1)) + stT130 54 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 53
    simpa using h
  have hprev := st130_p53
  have hstep := st130_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p55 : ((340742465979/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT130 (i+1))
      = (∑ i ∈ Finset.range 54, stT130 (i+1)) + stT130 55 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 54
    simpa using h
  have hprev := st130_p54
  have hstep := st130_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p56 : ((7742979757131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT130 (i+1))
      = (∑ i ∈ Finset.range 55, stT130 (i+1)) + stT130 56 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 55
    simpa using h
  have hprev := st130_p55
  have hstep := st130_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p57 : ((1862982050061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT130 (i+1))
      = (∑ i ∈ Finset.range 56, stT130 (i+1)) + stT130 57 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 56
    simpa using h
  have hprev := st130_p56
  have hstep := st130_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p58 : ((2155838981439/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT130 (i+1))
      = (∑ i ∈ Finset.range 57, stT130 (i+1)) + stT130 58 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 57
    simpa using h
  have hprev := st130_p57
  have hstep := st130_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p59 : ((931423992997/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT130 (i+1))
      = (∑ i ∈ Finset.range 58, stT130 (i+1)) + stT130 59 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 58
    simpa using h
  have hprev := st130_p58
  have hstep := st130_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p60 : ((153227984579/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT130 (i+1))
      = (∑ i ∈ Finset.range 59, stT130 (i+1)) + stT130 60 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 59
    simpa using h
  have hprev := st130_p59
  have hstep := st130_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p61 : ((4302792422147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT130 (i+1))
      = (∑ i ∈ Finset.range 60, stT130 (i+1)) + stT130 61 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 60
    simpa using h
  have hprev := st130_p60
  have hstep := st130_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p62 : ((115425032431/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT130 (i+1))
      = (∑ i ∈ Finset.range 61, stT130 (i+1)) + stT130 62 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 61
    simpa using h
  have hprev := st130_p61
  have hstep := st130_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p63 : ((7665755465279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT130 (i+1))
      = (∑ i ∈ Finset.range 62, stT130 (i+1)) + stT130 63 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 62
    simpa using h
  have hprev := st130_p62
  have hstep := st130_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p64 : ((8622171715279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT130 (i+1))
      = (∑ i ∈ Finset.range 63, stT130 (i+1)) + stT130 64 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 63
    simpa using h
  have hprev := st130_p63
  have hstep := st130_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p65 : ((1498582352571/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT130 (i+1))
      = (∑ i ∈ Finset.range 64, stT130 (i+1)) + stT130 65 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 64
    simpa using h
  have hprev := st130_p64
  have hstep := st130_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p66 : ((149546887617/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT130 (i+1))
      = (∑ i ∈ Finset.range 65, stT130 (i+1)) + stT130 66 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 65
    simpa using h
  have hprev := st130_p65
  have hstep := st130_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p67 : ((4307811778959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT130 (i+1))
      = (∑ i ∈ Finset.range 66, stT130 (i+1)) + stT130 67 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 66
    simpa using h
  have hprev := st130_p66
  have hstep := st130_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p68 : ((1561970101523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT130 (i+1))
      = (∑ i ∈ Finset.range 67, stT130 (i+1)) + stT130 68 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 67
    simpa using h
  have hprev := st130_p67
  have hstep := st130_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p69 : ((7214703549221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT130 (i+1))
      = (∑ i ∈ Finset.range 68, stT130 (i+1)) + stT130 69 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 68
    simpa using h
  have hprev := st130_p68
  have hstep := st130_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p70 : ((8381760025261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT130 (i+1))
      = (∑ i ∈ Finset.range 69, stT130 (i+1)) + stT130 70 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 69
    simpa using h
  have hprev := st130_p69
  have hstep := st130_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p71 : ((8315408230423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT130 (i+1))
      = (∑ i ∈ Finset.range 70, stT130 (i+1)) + stT130 71 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 70
    simpa using h
  have hprev := st130_p70
  have hstep := st130_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p72 : ((7190632842087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT130 (i+1))
      = (∑ i ∈ Finset.range 71, stT130 (i+1)) + stT130 72 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 71
    simpa using h
  have hprev := st130_p71
  have hstep := st130_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p73 : ((7777851449007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT130 (i+1))
      = (∑ i ∈ Finset.range 72, stT130 (i+1)) + stT130 73 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 72
    simpa using h
  have hprev := st130_p72
  have hstep := st130_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p74 : ((345960113043/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT130 (i+1))
      = (∑ i ∈ Finset.range 73, stT130 (i+1)) + stT130 74 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 73
    simpa using h
  have hprev := st130_p73
  have hstep := st130_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p75 : ((7746031262879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT130 (i+1))
      = (∑ i ∈ Finset.range 74, stT130 (i+1)) + stT130 75 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 74
    simpa using h
  have hprev := st130_p74
  have hstep := st130_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p76 : ((7174088496847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT130 (i+1))
      = (∑ i ∈ Finset.range 75, stT130 (i+1)) + stT130 76 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 75
    simpa using h
  have hprev := st130_p75
  have hstep := st130_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p77 : ((2056650365983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT130 (i+1))
      = (∑ i ∈ Finset.range 76, stT130 (i+1)) + stT130 77 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 76
    simpa using h
  have hprev := st130_p76
  have hstep := st130_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p78 : ((4273376392841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT130 (i+1))
      = (∑ i ∈ Finset.range 77, stT130 (i+1)) + stT130 78 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 77
    simpa using h
  have hprev := st130_p77
  have hstep := st130_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p79 : ((3722178905321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT130 (i+1))
      = (∑ i ∈ Finset.range 78, stT130 (i+1)) + stT130 79 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 78
    simpa using h
  have hprev := st130_p78
  have hstep := st130_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p80 : ((36458099159/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT130 (i+1))
      = (∑ i ∈ Finset.range 79, stT130 (i+1)) + stT130 80 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 79
    simpa using h
  have hprev := st130_p79
  have hstep := st130_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p81 : ((8397887498951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT130 (i+1))
      = (∑ i ∈ Finset.range 80, stT130 (i+1)) + stT130 81 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 80
    simpa using h
  have hprev := st130_p80
  have hstep := st130_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p82 : ((8473469026181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT130 (i+1))
      = (∑ i ∈ Finset.range 81, stT130 (i+1)) + stT130 82 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 81
    simpa using h
  have hprev := st130_p81
  have hstep := st130_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p83 : ((28820262833/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT130 (i+1))
      = (∑ i ∈ Finset.range 82, stT130 (i+1)) + stT130 83 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 82
    simpa using h
  have hprev := st130_p82
  have hstep := st130_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p84 : ((3646752638819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT130 (i+1))
      = (∑ i ∈ Finset.range 83, stT130 (i+1)) + stT130 84 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 83
    simpa using h
  have hprev := st130_p83
  have hstep := st130_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p85 : ((167431490493/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT130 (i+1))
      = (∑ i ∈ Finset.range 84, stT130 (i+1)) + stT130 85 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 84
    simpa using h
  have hprev := st130_p84
  have hstep := st130_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p86 : ((2135853639679/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT130 (i+1))
      = (∑ i ∈ Finset.range 85, stT130 (i+1)) + stT130 86 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 85
    simpa using h
  have hprev := st130_p85
  have hstep := st130_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p87 : ((1499797346543/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT130 (i+1))
      = (∑ i ∈ Finset.range 86, stT130 (i+1)) + stT130 87 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 86
    simpa using h
  have hprev := st130_p86
  have hstep := st130_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p88 : ((7170659632723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT130 (i+1))
      = (∑ i ∈ Finset.range 87, stT130 (i+1)) + stT130 88 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 87
    simpa using h
  have hprev := st130_p87
  have hstep := st130_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p89 : ((8140671367399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT130 (i+1))
      = (∑ i ∈ Finset.range 88, stT130 (i+1)) + stT130 89 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 88
    simpa using h
  have hprev := st130_p88
  have hstep := st130_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p90 : ((8676372516811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT130 (i+1))
      = (∑ i ∈ Finset.range 89, stT130 (i+1)) + stT130 90 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 89
    simpa using h
  have hprev := st130_p89
  have hstep := st130_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p91 : ((7853013836121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT130 (i+1))
      = (∑ i ∈ Finset.range 90, stT130 (i+1)) + stT130 91 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 90
    simpa using h
  have hprev := st130_p90
  have hstep := st130_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p92 : ((7092469343497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT130 (i+1))
      = (∑ i ∈ Finset.range 91, stT130 (i+1)) + stT130 92 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 91
    simpa using h
  have hprev := st130_p91
  have hstep := st130_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p93 : ((3833770296063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT130 (i+1))
      = (∑ i ∈ Finset.range 92, stT130 (i+1)) + stT130 93 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 92
    simpa using h
  have hprev := st130_p92
  have hstep := st130_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p94 : ((8614447986807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT130 (i+1))
      = (∑ i ∈ Finset.range 93, stT130 (i+1)) + stT130 94 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 93
    simpa using h
  have hprev := st130_p93
  have hstep := st130_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p95 : ((839812749651/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT130 (i+1))
      = (∑ i ∈ Finset.range 94, stT130 (i+1)) + stT130 95 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 94
    simpa using h
  have hprev := st130_p94
  have hstep := st130_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p96 : ((922182443493/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT130 (i+1))
      = (∑ i ∈ Finset.range 95, stT130 (i+1)) + stT130 96 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 95
    simpa using h
  have hprev := st130_p95
  have hstep := st130_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p97 : ((3577532016573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT130 (i+1))
      = (∑ i ∈ Finset.range 96, stT130 (i+1)) + stT130 97 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 96
    simpa using h
  have hprev := st130_p96
  have hstep := st130_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p98 : ((4030478617537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT130 (i+1))
      = (∑ i ∈ Finset.range 97, stT130 (i+1)) + stT130 98 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 97
    simpa using h
  have hprev := st130_p97
  have hstep := st130_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p99 : ((4357710624441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT130 (i+1))
      = (∑ i ∈ Finset.range 98, stT130 (i+1)) + stT130 99 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 98
    simpa using h
  have hprev := st130_p98
  have hstep := st130_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p100 : ((4076467124441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT130 (i+1))
      = (∑ i ∈ Finset.range 99, stT130 (i+1)) + stT130 100 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 99
    simpa using h
  have hprev := st130_p99
  have hstep := st130_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p101 : ((3604193233539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT130 (i+1))
      = (∑ i ∈ Finset.range 100, stT130 (i+1)) + stT130 101 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 100
    simpa using h
  have hprev := st130_p100
  have hstep := st130_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p102 : ((1809531135519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT130 (i+1))
      = (∑ i ∈ Finset.range 101, stT130 (i+1)) + stT130 102 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 101
    simpa using h
  have hprev := st130_p101
  have hstep := st130_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p103 : ((4093534641711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT130 (i+1))
      = (∑ i ∈ Finset.range 102, stT130 (i+1)) + stT130 103 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 102
    simpa using h
  have hprev := st130_p102
  have hstep := st130_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p104 : ((4365132258081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT130 (i+1))
      = (∑ i ∈ Finset.range 103, stT130 (i+1)) + stT130 104 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 103
    simpa using h
  have hprev := st130_p103
  have hstep := st130_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p105 : ((813428958267/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT130 (i+1))
      = (∑ i ∈ Finset.range 104, stT130 (i+1)) + stT130 105 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 104
    simpa using h
  have hprev := st130_p104
  have hstep := st130_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p106 : ((901468203501/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT130 (i+1))
      = (∑ i ∈ Finset.range 105, stT130 (i+1)) + stT130 106 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 105
    simpa using h
  have hprev := st130_p105
  have hstep := st130_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p107 : ((3590471726857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT130 (i+1))
      = (∑ i ∈ Finset.range 106, stT130 (i+1)) + stT130 107 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 106
    simpa using h
  have hprev := st130_p106
  have hstep := st130_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p108 : ((1008709573933/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT130 (i+1))
      = (∑ i ∈ Finset.range 107, stT130 (i+1)) + stT130 108 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 107
    simpa using h
  have hprev := st130_p107
  have hstep := st130_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p109 : ((136462610827/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT130 (i+1))
      = (∑ i ∈ Finset.range 108, stT130 (i+1)) + stT130 109 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 108
    simpa using h
  have hprev := st130_p108
  have hstep := st130_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p110 : ((1042956997667/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT130 (i+1))
      = (∑ i ∈ Finset.range 109, stT130 (i+1)) + stT130 110 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 109
    simpa using h
  have hprev := st130_p109
  have hstep := st130_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p111 : ((1848699004237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT130 (i+1))
      = (∑ i ∈ Finset.range 110, stT130 (i+1)) + stT130 111 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 110
    simpa using h
  have hprev := st130_p110
  have hstep := st130_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p112 : ((1761525675221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT130 (i+1))
      = (∑ i ∈ Finset.range 111, stT130 (i+1)) + stT130 112 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 111
    simpa using h
  have hprev := st130_p111
  have hstep := st130_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p113 : ((1926520672641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT130 (i+1))
      = (∑ i ∈ Finset.range 112, stT130 (i+1)) + stT130 113 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 112
    simpa using h
  have hprev := st130_p112
  have hstep := st130_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p114 : ((8585113605729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT130 (i+1))
      = (∑ i ∈ Finset.range 113, stT130 (i+1)) + stT130 114 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 113
    simpa using h
  have hprev := st130_p113
  have hstep := st130_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p115 : ((8662530087809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT130 (i+1))
      = (∑ i ∈ Finset.range 114, stT130 (i+1)) + stT130 115 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 114
    simpa using h
  have hprev := st130_p114
  have hstep := st130_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p116 : ((7860647212851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT130 (i+1))
      = (∑ i ∈ Finset.range 115, stT130 (i+1)) + stT130 116 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 115
    simpa using h
  have hprev := st130_p115
  have hstep := st130_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p117 : ((1772774300739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT130 (i+1))
      = (∑ i ∈ Finset.range 116, stT130 (i+1)) + stT130 117 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 116
    simpa using h
  have hprev := st130_p116
  have hstep := st130_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p118 : ((36020285781/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT130 (i+1))
      = (∑ i ∈ Finset.range 117, stT130 (i+1)) + stT130 118 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 117
    simpa using h
  have hprev := st130_p117
  have hstep := st130_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p119 : ((4032458165463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT130 (i+1))
      = (∑ i ∈ Finset.range 118, stT130 (i+1)) + stT130 119 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 118
    simpa using h
  have hprev := st130_p118
  have hstep := st130_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p120 : ((4370360647443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT130 (i+1))
      = (∑ i ∈ Finset.range 119, stT130 (i+1)) + stT130 120 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 119
    simpa using h
  have hprev := st130_p119
  have hstep := st130_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p121 : ((4259978818223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT130 (i+1))
      = (∑ i ∈ Finset.range 120, stT130 (i+1)) + stT130 121 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 120
    simpa using h
  have hprev := st130_p120
  have hstep := st130_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p122 : ((3821982914267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT130 (i+1))
      = (∑ i ∈ Finset.range 121, stT130 (i+1)) + stT130 122 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 121
    simpa using h
  have hprev := st130_p121
  have hstep := st130_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p123 : ((877422264733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT130 (i+1))
      = (∑ i ∈ Finset.range 122, stT130 (i+1)) + stT130 123 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 122
    simpa using h
  have hprev := st130_p122
  have hstep := st130_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p124 : ((3636977509237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT130 (i+1))
      = (∑ i ∈ Finset.range 123, stT130 (i+1)) + stT130 124 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 123
    simpa using h
  have hprev := st130_p123
  have hstep := st130_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p125 : ((2035721370603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT130 (i+1))
      = (∑ i ∈ Finset.range 124, stT130 (i+1)) + stT130 125 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 124
    simpa using h
  have hprev := st130_p124
  have hstep := st130_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p126 : ((2191400012233/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT130 (i+1))
      = (∑ i ∈ Finset.range 125, stT130 (i+1)) + stT130 126 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 125
    simpa using h
  have hprev := st130_p125
  have hstep := st130_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p127 : ((1708585159199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT130 (i+1))
      = (∑ i ∈ Finset.range 126, stT130 (i+1)) + stT130 127 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 126
    simpa using h
  have hprev := st130_p126
  have hstep := st130_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p128 : ((7697845187479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT130 (i+1))
      = (∑ i ∈ Finset.range 127, stT130 (i+1)) + stT130 128 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 127
    simpa using h
  have hprev := st130_p127
  have hstep := st130_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p129 : ((70324628337/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT130 (i+1))
      = (∑ i ∈ Finset.range 128, stT130 (i+1)) + stT130 129 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 128
    simpa using h
  have hprev := st130_p128
  have hstep := st130_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p130 : ((3580514944431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT130 (i+1))
      = (∑ i ∈ Finset.range 129, stT130 (i+1)) + stT130 130 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 129
    simpa using h
  have hprev := st130_p129
  have hstep := st130_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p131 : ((3978039779983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT130 (i+1))
      = (∑ i ∈ Finset.range 130, stT130 (i+1)) + stT130 131 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 130
    simpa using h
  have hprev := st130_p130
  have hstep := st130_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p132 : ((4346472844413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT130 (i+1))
      = (∑ i ∈ Finset.range 131, stT130 (i+1)) + stT130 132 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 131
    simpa using h
  have hprev := st130_p131
  have hstep := st130_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p133 : ((2179405469187/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT130 (i+1))
      = (∑ i ∈ Finset.range 132, stT130 (i+1)) + stT130 133 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 132
    simpa using h
  have hprev := st130_p132
  have hstep := st130_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p134 : ((1603455446273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT130 (i+1))
      = (∑ i ∈ Finset.range 133, stT130 (i+1)) + stT130 134 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 133
    simpa using h
  have hprev := st130_p133
  have hstep := st130_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p135 : ((7206133337733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT130 (i+1))
      = (∑ i ∈ Finset.range 134, stT130 (i+1)) + stT130 135 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 134
    simpa using h
  have hprev := st130_p134
  have hstep := st130_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p136 : ((6977069517657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT130 (i+1))
      = (∑ i ∈ Finset.range 135, stT130 (i+1)) + stT130 136 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 135
    simpa using h
  have hprev := st130_p135
  have hstep := st130_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p137 : ((7515587821897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT130 (i+1))
      = (∑ i ∈ Finset.range 136, stT130 (i+1)) + stT130 137 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 136
    simpa using h
  have hprev := st130_p136
  have hstep := st130_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p138 : ((8365434141961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT130 (i+1))
      = (∑ i ∈ Finset.range 137, stT130 (i+1)) + stT130 138 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 137
    simpa using h
  have hprev := st130_p137
  have hstep := st130_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p139 : ((8827002784177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT130 (i+1))
      = (∑ i ∈ Finset.range 138, stT130 (i+1)) + stT130 139 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 138
    simpa using h
  have hprev := st130_p138
  have hstep := st130_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p140 : ((8532058901967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT130 (i+1))
      = (∑ i ∈ Finset.range 139, stT130 (i+1)) + stT130 140 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 139
    simpa using h
  have hprev := st130_p139
  have hstep := st130_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p141 : ((7724814102367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT130 (i+1))
      = (∑ i ∈ Finset.range 140, stT130 (i+1)) + stT130 141 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 140
    simpa using h
  have hprev := st130_p140
  have hstep := st130_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p142 : ((7046509166041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT130 (i+1))
      = (∑ i ∈ Finset.range 141, stT130 (i+1)) + stT130 142 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 141
    simpa using h
  have hprev := st130_p141
  have hstep := st130_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p143 : ((3511162091119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT130 (i+1))
      = (∑ i ∈ Finset.range 142, stT130 (i+1)) + stT130 143 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 142
    simpa using h
  have hprev := st130_p142
  have hstep := st130_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p144 : ((957874032413/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT130 (i+1))
      = (∑ i ∈ Finset.range 143, stT130 (i+1)) + stT130 144 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 143
    simpa using h
  have hprev := st130_p143
  have hstep := st130_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p145 : ((4237930697927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT130 (i+1))
      = (∑ i ∈ Finset.range 144, stT130 (i+1)) + stT130 145 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 144
    simpa using h
  have hprev := st130_p144
  have hstep := st130_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p146 : ((8851669377909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT130 (i+1))
      = (∑ i ∈ Finset.range 145, stT130 (i+1)) + stT130 146 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 145
    simpa using h
  have hprev := st130_p145
  have hstep := st130_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p147 : ((8518358105043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT130 (i+1))
      = (∑ i ∈ Finset.range 146, stT130 (i+1)) + stT130 147 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 146
    simpa using h
  have hprev := st130_p146
  have hstep := st130_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p148 : ((7726868983483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT130 (i+1))
      = (∑ i ∈ Finset.range 147, stT130 (i+1)) + stT130 148 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 147
    simpa using h
  have hprev := st130_p147
  have hstep := st130_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p149 : ((1410318649951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT130 (i+1))
      = (∑ i ∈ Finset.range 148, stT130 (i+1)) + stT130 149 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 148
    simpa using h
  have hprev := st130_p148
  have hstep := st130_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p150 : ((3485311029381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT130 (i+1))
      = (∑ i ∈ Finset.range 149, stT130 (i+1)) + stT130 150 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 149
    simpa using h
  have hprev := st130_p149
  have hstep := st130_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p151 : ((3766937828753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT130 (i+1))
      = (∑ i ∈ Finset.range 150, stT130 (i+1)) + stT130 151 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 150
    simpa using h
  have hprev := st130_p150
  have hstep := st130_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p152 : ((4171926798281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT130 (i+1))
      = (∑ i ∈ Finset.range 151, stT130 (i+1)) + stT130 152 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 151
    simpa using h
  have hprev := st130_p151
  have hstep := st130_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p153 : ((4421822545289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT130 (i+1))
      = (∑ i ∈ Finset.range 152, stT130 (i+1)) + stT130 153 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 152
    simpa using h
  have hprev := st130_p152
  have hstep := st130_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p154 : ((347961251567/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT130 (i+1))
      = (∑ i ∈ Finset.range 153, stT130 (i+1)) + stT130 154 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 153
    simpa using h
  have hprev := st130_p153
  have hstep := st130_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p155 : ((320552011643/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT130 (i+1))
      = (∑ i ∈ Finset.range 154, stT130 (i+1)) + stT130 155 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 154
    simpa using h
  have hprev := st130_p154
  have hstep := st130_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p156 : ((7245875083617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT130 (i+1))
      = (∑ i ∈ Finset.range 155, stT130 (i+1)) + stT130 156 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 155
    simpa using h
  have hprev := st130_p155
  have hstep := st130_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p157 : ((1724119146363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT130 (i+1))
      = (∑ i ∈ Finset.range 156, stT130 (i+1)) + stT130 157 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 156
    simpa using h
  have hprev := st130_p156
  have hstep := st130_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p158 : ((7185832599707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT130 (i+1))
      = (∑ i ∈ Finset.range 157, stT130 (i+1)) + stT130 158 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 157
    simpa using h
  have hprev := st130_p157
  have hstep := st130_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p159 : ((7922772069253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT130 (i+1))
      = (∑ i ∈ Finset.range 158, stT130 (i+1)) + stT130 159 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 158
    simpa using h
  have hprev := st130_p158
  have hstep := st130_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p160 : ((2159772509551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT130 (i+1))
      = (∑ i ∈ Finset.range 159, stT130 (i+1)) + stT130 160 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 159
    simpa using h
  have hprev := st130_p159
  have hstep := st130_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p161 : ((2222502913111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT130 (i+1))
      = (∑ i ∈ Finset.range 160, stT130 (i+1)) + stT130 161 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 160
    simpa using h
  have hprev := st130_p160
  have hstep := st130_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p162 : ((66613663823/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT130 (i+1))
      = (∑ i ∈ Finset.range 161, stT130 (i+1)) + stT130 162 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 161
    simpa using h
  have hprev := st130_p161
  have hstep := st130_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p163 : ((7775933504563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT130 (i+1))
      = (∑ i ∈ Finset.range 162, stT130 (i+1)) + stT130 163 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 162
    simpa using h
  have hprev := st130_p162
  have hstep := st130_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p164 : ((7092573178331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT130 (i+1))
      = (∑ i ∈ Finset.range 163, stT130 (i+1)) + stT130 164 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 163
    simpa using h
  have hprev := st130_p163
  have hstep := st130_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p165 : ((6880889958243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT130 (i+1))
      = (∑ i ∈ Finset.range 164, stT130 (i+1)) + stT130 165 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 164
    simpa using h
  have hprev := st130_p164
  have hstep := st130_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p166 : ((7259866927943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT130 (i+1))
      = (∑ i ∈ Finset.range 165, stT130 (i+1)) + stT130 166 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 165
    simpa using h
  have hprev := st130_p165
  have hstep := st130_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p167 : ((8003551069739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT130 (i+1))
      = (∑ i ∈ Finset.range 166, stT130 (i+1)) + stT130 167 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 166
    simpa using h
  have hprev := st130_p166
  have hstep := st130_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p168 : ((8681952032183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT130 (i+1))
      = (∑ i ∈ Finset.range 167, stT130 (i+1)) + stT130 168 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 167
    simpa using h
  have hprev := st130_p167
  have hstep := st130_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p169 : ((8911433341163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT130 (i+1))
      = (∑ i ∈ Finset.range 168, stT130 (i+1)) + stT130 169 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 168
    simpa using h
  have hprev := st130_p168
  have hstep := st130_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p170 : ((8568176621483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT130 (i+1))
      = (∑ i ∈ Finset.range 169, stT130 (i+1)) + stT130 170 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 169
    simpa using h
  have hprev := st130_p169
  have hstep := st130_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p171 : ((7848314331963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT130 (i+1))
      = (∑ i ∈ Finset.range 170, stT130 (i+1)) + stT130 171 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 170
    simpa using h
  have hprev := st130_p170
  have hstep := st130_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p172 : ((7150093391919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT130 (i+1))
      = (∑ i ∈ Finset.range 171, stT130 (i+1)) + stT130 172 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 171
    simpa using h
  have hprev := st130_p171
  have hstep := st130_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p173 : ((6851523757717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT130 (i+1))
      = (∑ i ∈ Finset.range 172, stT130 (i+1)) + stT130 173 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 172
    simpa using h
  have hprev := st130_p172
  have hstep := st130_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p174 : ((7108415878389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT130 (i+1))
      = (∑ i ∈ Finset.range 173, stT130 (i+1)) + stT130 174 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 173
    simpa using h
  have hprev := st130_p173
  have hstep := st130_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p175 : ((7778867319789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT130 (i+1))
      = (∑ i ∈ Finset.range 174, stT130 (i+1)) + stT130 175 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 174
    simpa using h
  have hprev := st130_p174
  have hstep := st130_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p176 : ((8507138226047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT130 (i+1))
      = (∑ i ∈ Finset.range 175, stT130 (i+1)) + stT130 176 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 175
    simpa using h
  have hprev := st130_p175
  have hstep := st130_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p177 : ((8914954286391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT130 (i+1))
      = (∑ i ∈ Finset.range 176, stT130 (i+1)) + stT130 177 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 176
    simpa using h
  have hprev := st130_p176
  have hstep := st130_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p178 : ((8796355088499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT130 (i+1))
      = (∑ i ∈ Finset.range 177, stT130 (i+1)) + stT130 178 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 177
    simpa using h
  have hprev := st130_p177
  have hstep := st130_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p179 : ((8216850766671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT130 (i+1))
      = (∑ i ∈ Finset.range 178, stT130 (i+1)) + stT130 179 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 178
    simpa using h
  have hprev := st130_p178
  have hstep := st130_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p180 : ((7472070926859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT130 (i+1))
      = (∑ i ∈ Finset.range 179, stT130 (i+1)) + stT130 180 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 179
    simpa using h
  have hprev := st130_p179
  have hstep := st130_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p181 : ((6933680059509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT130 (i+1))
      = (∑ i ∈ Finset.range 180, stT130 (i+1)) + stT130 181 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 180
    simpa using h
  have hprev := st130_p180
  have hstep := st130_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p182 : ((6864259032009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT130 (i+1))
      = (∑ i ∈ Finset.range 181, stT130 (i+1)) + stT130 182 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 181
    simpa using h
  have hprev := st130_p181
  have hstep := st130_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p183 : ((7292888936649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT130 (i+1))
      = (∑ i ∈ Finset.range 182, stT130 (i+1)) + stT130 183 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 182
    simpa using h
  have hprev := st130_p182
  have hstep := st130_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p184 : ((160165368819/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT130 (i+1))
      = (∑ i ∈ Finset.range 183, stT130 (i+1)) + stT130 184 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 183
    simpa using h
  have hprev := st130_p183
  have hstep := st130_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p185 : ((2166685384711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT130 (i+1))
      = (∑ i ∈ Finset.range 184, stT130 (i+1)) + stT130 185 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 184
    simpa using h
  have hprev := st130_p184
  have hstep := st130_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p186 : ((8958396758619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT130 (i+1))
      = (∑ i ∈ Finset.range 185, stT130 (i+1)) + stT130 186 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 185
    simpa using h
  have hprev := st130_p185
  have hstep := st130_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p187 : ((8750704988797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT130 (i+1))
      = (∑ i ∈ Finset.range 186, stT130 (i+1)) + stT130 187 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 186
    simpa using h
  have hprev := st130_p186
  have hstep := st130_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p188 : ((8144456499847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT130 (i+1))
      = (∑ i ∈ Finset.range 187, stT130 (i+1)) + stT130 188 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 187
    simpa using h
  have hprev := st130_p187
  have hstep := st130_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p189 : ((7420669914341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT130 (i+1))
      = (∑ i ∈ Finset.range 188, stT130 (i+1)) + stT130 189 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 188
    simpa using h
  have hprev := st130_p188
  have hstep := st130_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p190 : ((1381604059603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT130 (i+1))
      = (∑ i ∈ Finset.range 189, stT130 (i+1)) + stT130 190 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 189
    simpa using h
  have hprev := st130_p189
  have hstep := st130_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p191 : ((1366826632093/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT130 (i+1))
      = (∑ i ∈ Finset.range 190, stT130 (i+1)) + stT130 191 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 190
    simpa using h
  have hprev := st130_p190
  have hstep := st130_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p192 : ((289101855791/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT130 (i+1))
      = (∑ i ∈ Finset.range 191, stT130 (i+1)) + stT130 192 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 191
    simpa using h
  have hprev := st130_p191
  have hstep := st130_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p193 : ((791104024969/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT130 (i+1))
      = (∑ i ∈ Finset.range 192, stT130 (i+1)) + stT130 193 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 192
    simpa using h
  have hprev := st130_p192
  have hstep := st130_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p194 : ((2146174880783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT130 (i+1))
      = (∑ i ∈ Finset.range 193, stT130 (i+1)) + stT130 194 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 193
    simpa using h
  have hprev := st130_p193
  have hstep := st130_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p195 : ((5599141901/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT130 (i+1))
      = (∑ i ∈ Finset.range 194, stT130 (i+1)) + stT130 195 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 194
    simpa using h
  have hprev := st130_p194
  have hstep := st130_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p196 : ((2219064966449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT130 (i+1))
      = (∑ i ∈ Finset.range 195, stT130 (i+1)) + stT130 196 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 195
    simpa using h
  have hprev := st130_p195
  have hstep := st130_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p197 : ((8376627465039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT130 (i+1))
      = (∑ i ∈ Finset.range 196, stT130 (i+1)) + stT130 197 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 196
    simpa using h
  have hprev := st130_p196
  have hstep := st130_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p198 : ((7672432379409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT130 (i+1))
      = (∑ i ∈ Finset.range 197, stT130 (i+1)) + stT130 198 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 197
    simpa using h
  have hprev := st130_p197
  have hstep := st130_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p199 : ((1411404428433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT130 (i+1))
      = (∑ i ∈ Finset.range 198, stT130 (i+1)) + stT130 199 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 198
    simpa using h
  have hprev := st130_p198
  have hstep := st130_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p200 : ((1695452079897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT130 (i+1))
      = (∑ i ∈ Finset.range 199, stT130 (i+1)) + stT130 200 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 199
    simpa using h
  have hprev := st130_p199
  have hstep := st130_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p201 : ((3477683460489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT130 (i+1))
      = (∑ i ∈ Finset.range 200, stT130 (i+1)) + stT130 201 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 200
    simpa using h
  have hprev := st130_p200
  have hstep := st130_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p202 : ((7503763791121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT130 (i+1))
      = (∑ i ∈ Finset.range 201, stT130 (i+1)) + stT130 202 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 201
    simpa using h
  have hprev := st130_p201
  have hstep := st130_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p203 : ((8205161158477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT130 (i+1))
      = (∑ i ∈ Finset.range 202, stT130 (i+1)) + stT130 203 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 202
    simpa using h
  have hprev := st130_p202
  have hstep := st130_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p204 : ((8781461795557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT130 (i+1))
      = (∑ i ∈ Finset.range 203, stT130 (i+1)) + stT130 204 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 203
    simpa using h
  have hprev := st130_p203
  have hstep := st130_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p205 : ((9008590533127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT130 (i+1))
      = (∑ i ∈ Finset.range 204, stT130 (i+1)) + stT130 205 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 204
    simpa using h
  have hprev := st130_p204
  have hstep := st130_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p206 : ((8801771315833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT130 (i+1))
      = (∑ i ∈ Finset.range 205, stT130 (i+1)) + stT130 206 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 205
    simpa using h
  have hprev := st130_p205
  have hstep := st130_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p207 : ((2061052663393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT130 (i+1))
      = (∑ i ∈ Finset.range 206, stT130 (i+1)) + stT130 207 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 206
    simpa using h
  have hprev := st130_p206
  have hstep := st130_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p208 : ((1887715597153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT130 (i+1))
      = (∑ i ∈ Finset.range 207, stT130 (i+1)) + stT130 208 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 207
    simpa using h
  have hprev := st130_p207
  have hstep := st130_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p209 : ((1745974893073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT130 (i+1))
      = (∑ i ∈ Finset.range 208, stT130 (i+1)) + stT130 209 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 208
    simpa using h
  have hprev := st130_p208
  have hstep := st130_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p210 : ((675361971763/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT130 (i+1))
      = (∑ i ∈ Finset.range 209, stT130 (i+1)) + stT130 210 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 209
    simpa using h
  have hprev := st130_p209
  have hstep := st130_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p211 : ((3471057028871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT130 (i+1))
      = (∑ i ∈ Finset.range 210, stT130 (i+1)) + stT130 211 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 210
    simpa using h
  have hprev := st130_p210
  have hstep := st130_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p212 : ((1869164902291/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT130 (i+1))
      = (∑ i ∈ Finset.range 211, stT130 (i+1)) + stT130 212 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 211
    simpa using h
  have hprev := st130_p211
  have hstep := st130_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p213 : ((2040069289567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT130 (i+1))
      = (∑ i ∈ Finset.range 212, stT130 (i+1)) + stT130 213 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 212
    simpa using h
  have hprev := st130_p212
  have hstep := st130_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p214 : ((4372940592939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT130 (i+1))
      = (∑ i ∈ Finset.range 213, stT130 (i+1)) + stT130 214 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 213
    simpa using h
  have hprev := st130_p213
  have hstep := st130_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p215 : ((56410530689/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT130 (i+1))
      = (∑ i ∈ Finset.range 214, stT130 (i+1)) + stT130 215 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 214
    simpa using h
  have hprev := st130_p214
  have hstep := st130_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p216 : ((1112942463827/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT130 (i+1))
      = (∑ i ∈ Finset.range 215, stT130 (i+1)) + stT130 216 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 215
    simpa using h
  have hprev := st130_p215
  have hstep := st130_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p217 : ((4212826597983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT130 (i+1))
      = (∑ i ∈ Finset.range 216, stT130 (i+1)) + stT130 217 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 216
    simpa using h
  have hprev := st130_p216
  have hstep := st130_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p218 : ((60631282803/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT130 (i+1))
      = (∑ i ∈ Finset.range 217, stT130 (i+1)) + stT130 218 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 217
    simpa using h
  have hprev := st130_p217
  have hstep := st130_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p219 : ((1784776917399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT130 (i+1))
      = (∑ i ∈ Finset.range 218, stT130 (i+1)) + stT130 219 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 218
    simpa using h
  have hprev := st130_p218
  have hstep := st130_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p220 : ((1692996891549/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT130 (i+1))
      = (∑ i ∈ Finset.range 219, stT130 (i+1)) + stT130 220 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 219
    simpa using h
  have hprev := st130_p219
  have hstep := st130_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p221 : ((1695310883229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT130 (i+1))
      = (∑ i ∈ Finset.range 220, stT130 (i+1)) + stT130 221 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 220
    simpa using h
  have hprev := st130_p220
  have hstep := st130_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p222 : ((895070683441/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT130 (i+1))
      = (∑ i ∈ Finset.range 221, stT130 (i+1)) + stT130 222 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 221
    simpa using h
  have hprev := st130_p221
  have hstep := st130_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p223 : ((3890478213193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT130 (i+1))
      = (∑ i ∈ Finset.range 222, stT130 (i+1)) + stT130 223 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 222
    simpa using h
  have hprev := st130_p222
  have hstep := st130_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p224 : ((2109075901497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT130 (i+1))
      = (∑ i ∈ Finset.range 223, stT130 (i+1)) + stT130 224 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 223
    simpa using h
  have hprev := st130_p223
  have hstep := st130_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p225 : ((557036862273/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT130 (i+1))
      = (∑ i ∈ Finset.range 224, stT130 (i+1)) + stT130 225 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 224
    simpa using h
  have hprev := st130_p224
  have hstep := st130_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p226 : ((566082781083/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT130 (i+1))
      = (∑ i ∈ Finset.range 225, stT130 (i+1)) + stT130 226 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 225
    simpa using h
  have hprev := st130_p225
  have hstep := st130_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p227 : ((1103357119739/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT130 (i+1))
      = (∑ i ∈ Finset.range 226, stT130 (i+1)) + stT130 227 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 226
    simpa using h
  have hprev := st130_p226
  have hstep := st130_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p228 : ((8297527475089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT130 (i+1))
      = (∑ i ∈ Finset.range 227, stT130 (i+1)) + stT130 228 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 227
    simpa using h
  have hprev := st130_p227
  have hstep := st130_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p229 : ((3819288305201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT130 (i+1))
      = (∑ i ∈ Finset.range 228, stT130 (i+1)) + stT130 229 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 228
    simpa using h
  have hprev := st130_p228
  have hstep := st130_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p230 : ((1764232509123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT130 (i+1))
      = (∑ i ∈ Finset.range 229, stT130 (i+1)) + stT130 230 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 229
    simpa using h
  have hprev := st130_p229
  have hstep := st130_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p231 : ((1683033007923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT130 (i+1))
      = (∑ i ∈ Finset.range 230, stT130 (i+1)) + stT130 231 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 230
    simpa using h
  have hprev := st130_p230
  have hstep := st130_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p232 : ((1690461339237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT130 (i+1))
      = (∑ i ∈ Finset.range 231, stT130 (i+1)) + stT130 232 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 231
    simpa using h
  have hprev := st130_p231
  have hstep := st130_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p233 : ((7134132932981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT130 (i+1))
      = (∑ i ∈ Finset.range 232, stT130 (i+1)) + stT130 233 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 232
    simpa using h
  have hprev := st130_p232
  have hstep := st130_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p234 : ((7733749758341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT130 (i+1))
      = (∑ i ∈ Finset.range 233, stT130 (i+1)) + stT130 234 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 233
    simpa using h
  have hprev := st130_p233
  have hstep := st130_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p235 : ((8379219181749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT130 (i+1))
      = (∑ i ∈ Finset.range 234, stT130 (i+1)) + stT130 235 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 234
    simpa using h
  have hprev := st130_p234
  have hstep := st130_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p236 : ((8878390380597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT130 (i+1))
      = (∑ i ∈ Finset.range 235, stT130 (i+1)) + stT130 236 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 235
    simpa using h
  have hprev := st130_p235
  have hstep := st130_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p237 : ((4542671856783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT130 (i+1))
      = (∑ i ∈ Finset.range 236, stT130 (i+1)) + stT130 237 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 236
    simpa using h
  have hprev := st130_p236
  have hstep := st130_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p238 : ((894191950371/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT130 (i+1))
      = (∑ i ∈ Finset.range 237, stT130 (i+1)) + stT130 238 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 237
    simpa using h
  have hprev := st130_p237
  have hstep := st130_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p239 : ((2123115113287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT130 (i+1))
      = (∑ i ∈ Finset.range 238, stT130 (i+1)) + stT130 239 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 238
    simpa using h
  have hprev := st130_p238
  have hstep := st130_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p240 : ((3934300741301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT130 (i+1))
      = (∑ i ∈ Finset.range 239, stT130 (i+1)) + stT130 240 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 239
    simpa using h
  have hprev := st130_p239
  have hstep := st130_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p241 : ((7249620070633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT130 (i+1))
      = (∑ i ∈ Finset.range 240, stT130 (i+1)) + stT130 241 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 240
    simpa using h
  have hprev := st130_p240
  have hstep := st130_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p242 : ((6810562881733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT130 (i+1))
      = (∑ i ∈ Finset.range 241, stT130 (i+1)) + stT130 242 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 241
    simpa using h
  have hprev := st130_p241
  have hstep := st130_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p243 : ((6673211102623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT130 (i+1))
      = (∑ i ∈ Finset.range 242, stT130 (i+1)) + stT130 243 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 242
    simpa using h
  have hprev := st130_p242
  have hstep := st130_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p244 : ((6873437611199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT130 (i+1))
      = (∑ i ∈ Finset.range 243, stT130 (i+1)) + stT130 244 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 243
    simpa using h
  have hprev := st130_p243
  have hstep := st130_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p245 : ((7353316541079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT130 (i+1))
      = (∑ i ∈ Finset.range 244, stT130 (i+1)) + stT130 245 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 244
    simpa using h
  have hprev := st130_p244
  have hstep := st130_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p246 : ((7979216611791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT130 (i+1))
      = (∑ i ∈ Finset.range 245, stT130 (i+1)) + stT130 246 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 245
    simpa using h
  have hprev := st130_p245
  have hstep := st130_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p247 : ((8579894159151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT130 (i+1))
      = (∑ i ∈ Finset.range 246, stT130 (i+1)) + stT130 247 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 246
    simpa using h
  have hprev := st130_p246
  have hstep := st130_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p248 : ((8993571259151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT130 (i+1))
      = (∑ i ∈ Finset.range 247, stT130 (i+1)) + stT130 248 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 247
    simpa using h
  have hprev := st130_p247
  have hstep := st130_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p249 : ((9111007921039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT130 (i+1))
      = (∑ i ∈ Finset.range 248, stT130 (i+1)) + stT130 249 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 248
    simpa using h
  have hprev := st130_p248
  have hstep := st130_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_p250 : ((1780655043603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT130 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT130 (i+1))
      = (∑ i ∈ Finset.range 249, stT130 (i+1)) + stT130 250 := by
    have h := Finset.sum_range_succ (fun i => stT130 (i+1)) 249
    simpa using h
  have hprev := st130_p249
  have hstep := st130_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st130_s250 :
    |Real.sin (((130 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))
      - ((944537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1190881/2500000) (δ := 331/50000000) (ψ := -398611/1000000) 130 114
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 130`** (evaluated boundary). -/
theorem station_130_sign : 0 < hardyG ((((130:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 130 250 (by norm_num) (by norm_num)
    ((-398611/1000000 : ℚ) : ℝ)
  have hchain := st130_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT130 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((130 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-398611/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st130_c250
  have hsinb := abs_le.mp st130_s250
  have hbdy_lo : ((-9694928538581/84501250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((130 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ))) / 2
          - ((((130:ℕ)):ℝ))
            * Real.sin (((130 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-398611/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((130:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((130:ℝ) * Real.log (250:ℝ) - ((-398611/1000000 : ℚ) : ℝ))) / 2
        - ((130:ℝ)) * Real.sin ((130:ℝ) * Real.log (250:ℝ) - ((-398611/1000000 : ℚ) : ℝ))
        ≥ ((-122632133/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((130:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-122632133/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-122632133/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-122632133/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((130:ℕ)):ℝ))+1) * (((((130:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((62243394411/156250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1780655043603/2000000000000 : ℚ) : ℝ) + ((-9694928538581/84501250000000 : ℚ) : ℝ)
      - ((62243394411/156250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-398611/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((130:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-398611/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((130:ℕ)):ℝ)))).re
      - Real.sin ((-398611/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((130:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((130:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((130:ℕ)):ℝ))
      = (((((130:ℕ)):ℝ)) * (Real.log ((((130:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((130:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_130
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
  have hθwin : |(((-398611/1000000 : ℚ) : ℝ) + ((21:ℤ)) * (2*Real.pi)) - theta ((((130:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((130:ℕ)):ℝ)))
    (φ := ((-398611/1000000 : ℚ) : ℝ) + ((21:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-398611/1000000 : ℚ)) : ℝ) 21).1,
    (cos_sin_shift (((-398611/1000000 : ℚ)) : ℝ) 21).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_130_sign
end AxiomAudit
