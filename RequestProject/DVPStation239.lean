import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 239` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT239 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((239 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((77237/100000 : ℚ) : ℝ))

theorem st239_c1 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((716259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77237/400000) (δ := 1/1000000000) (ψ := 77237/100000) 239 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t1 : ((716209/1000000 : ℚ) : ℝ) ≤ stT239 1 := by
  have hc : ((716209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((716209/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((716209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c2 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((21901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 954363/2500000) (δ := 2403/200000000) (ψ := 77237/100000) 239 26
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t2 : ((38671665423/1250000000000 : ℚ) : ℝ) ≤ stT239 2 := by
  have hc : ((5469/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38671665423/1250000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((5469/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c3 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-62871/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5244563/10000000) (δ := 3/250000) (ψ := 77237/100000) 239 42
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t3 : ((-1452087966027/5000000000000 : ℚ) : ℝ) ≤ stT239 3 := by
  have hc : ((-251509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1452087966027/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-251509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c4 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-774577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -767763/1250000) (δ := 5991/500000000) (ψ := 77237/100000) 239 53
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t4 : ((-3873135774627/10000000000000 : ℚ) : ℝ) ≤ stT239 4 := by
  have hc : ((-774627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3873135774627/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-774627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c5 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((820223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1522491/10000000) (δ := 12039/1000000000) (ψ := 77237/100000) 239 61
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t5 : ((733584875871/2000000000000 : ℚ) : ℝ) ≤ stT239 5 := by
  have hc : ((820173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((733584875871/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((820173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c6 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((12247/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125961/2500000) (δ := 12013/1000000000) (ψ := 77237/100000) 239 68
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t6 : ((199982422011/500000000000 : ℚ) : ℝ) ≤ stT239 6 := by
  have hc : ((97971/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199982422011/500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((97971/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c7 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((792709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409723/2500000) (δ := 12033/1000000000) (ψ := 77237/100000) 239 74
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t7 : ((748992208349/2500000000000 : ℚ) : ℝ) ≤ stT239 7 := by
  have hc : ((792659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((748992208349/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((792659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c8 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((493813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -393697/10000000) (δ := 11969/1000000000) (ψ := 77237/100000) 239 79
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t8 : ((436450942251/1250000000000 : ℚ) : ℝ) ≤ stT239 8 := by
  have hc : ((123447/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436450942251/1250000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((123447/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c9 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-960591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223431/312500) (δ := 6053/500000000) (ψ := 77237/100000) 239 83
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t9 : ((-1601068653547/5000000000000 : ℚ) : ℝ) ≤ stT239 9 := by
  have hc : ((-960641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1601068653547/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-960641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c10 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-972919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3635419/5000000) (δ := 11977/1000000000) (ψ := 77237/100000) 239 87
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t10 : ((-1538399231691/5000000000000 : ℚ) : ℝ) ≤ stT239 10 := by
  have hc : ((-972969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1538399231691/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-972969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c11 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((425021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1386829/10000000) (δ := 3037/250000000) (ψ := 77237/100000) 239 91
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t11 : ((320352741137/1250000000000 : ℚ) : ℝ) ≤ stT239 11 := by
  have hc : ((106249/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320352741137/1250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((106249/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c12 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-400841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6252251/10000000) (δ := 12027/1000000000) (ψ := 77237/100000) 239 94
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t12 : ((-18081261363/78125000000 : ℚ) : ℝ) ≤ stT239 12 := by
  have hc : ((-200433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18081261363/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-200433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c13 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-467941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55631/80000) (δ := 6049/500000000) (ψ := 77237/100000) 239 97
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t13 : ((-648952084483/2500000000000 : ℚ) : ℝ) ≤ stT239 13 := by
  have hc : ((-233983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-648952084483/2500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-233983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c14 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-14589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 821903/2000000) (δ := 12019/1000000000) (ψ := 77237/100000) 239 100
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t14 : ((-39017477187/2000000000000 : ℚ) : ℝ) ≤ stT239 14 := by
  have hc : ((-14599/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39017477187/2000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-14599/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c15 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((23567/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1791117/10000000) (δ := 12041/1000000000) (ψ := 77237/100000) 239 103
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t15 : ((243382707359/1250000000000 : ℚ) : ℝ) ≤ stT239 15 := by
  have hc : ((377047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243382707359/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((377047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c16 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-540547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535471/1000000) (δ := 2391/200000000) (ψ := 77237/100000) 239 105
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t16 : ((-1351493040597/10000000000000 : ℚ) : ℝ) ≤ stT239 16 := by
  have hc : ((-540597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1351493040597/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-540597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c17 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-603271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5545981/10000000) (δ := 12077/1000000000) (ψ := 77237/100000) 239 108
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t17 : ((-1463268810597/10000000000000 : ℚ) : ℝ) ≤ stT239 17 := by
  have hc : ((-603321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1463268810597/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-603321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c18 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((108041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702441/2500000) (δ := 3003/250000000) (ψ := 77237/100000) 239 110
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t18 : ((254625551127/2500000000000 : ℚ) : ℝ) ≤ stT239 18 := by
  have hc : ((216057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254625551127/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((216057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c19 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((44947/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -960269/5000000) (δ := 6053/500000000) (ψ := 77237/100000) 239 112
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t19 : ((824866443507/5000000000000 : ℚ) : ℝ) ≤ stT239 19 := by
  have hc : ((359551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((824866443507/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((359551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c20 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((59413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1344359/5000000) (δ := 601/50000000) (ψ := 77237/100000) 239 114
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t20 : ((531349893009/5000000000000 : ℚ) : ℝ) ≤ stT239 20 := by
  have hc : ((237627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531349893009/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((237627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c21 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-99699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1981/4000) (δ := 6017/500000000) (ψ := 77237/100000) 239 116
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t21 : ((-435176682717/5000000000000 : ℚ) : ℝ) ≤ stT239 21 := by
  have hc : ((-199423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435176682717/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-199423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c22 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-239739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7135237/10000000) (δ := 6071/500000000) (ψ := 77237/100000) 239 117
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t22 : ((-127788029003/625000000000 : ℚ) : ℝ) ≤ stT239 22 := by
  have hc : ((-479503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127788029003/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-479503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c23 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((1531/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113963/500000) (δ := 12147/1000000000) (ψ := 77237/100000) 239 119
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t23 : ((3192094821/25000000000 : ℚ) : ℝ) ≤ stT239 23 := by
  have hc : ((12247/20000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3192094821/25000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((12247/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c24 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((87761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -741461/2000000) (δ := 1197/100000000) (ψ := 77237/100000) 239 121
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t24 : ((179039289351/10000000000000 : ℚ) : ℝ) ≤ stT239 24 := by
  have hc : ((87711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179039289351/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((87711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c25 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-203677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4975877/10000000) (δ := 12077/1000000000) (ψ := 77237/100000) 239 122
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t25 : ((-203702101851/2500000000000 : ℚ) : ℝ) ≤ stT239 25 := by
  have hc : ((-101851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203702101851/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-101851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c26 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((180119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502841/5000000) (δ := 12111/1000000000) (ψ := 77237/100000) 239 124
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t26 : ((176596664567/2500000000000 : ℚ) : ℝ) ≤ stT239 26 := by
  have hc : ((90047/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176596664567/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((90047/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c27 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((7263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 479523/1250000) (δ := 1513/125000000) (ψ := 77237/100000) 239 125
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t27 : ((27916797/4000000000 : ℚ) : ℝ) ≤ stT239 27 := by
  have hc : ((7253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27916797/4000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((7253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c28 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-27823/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5850041/10000000) (δ := 12113/1000000000) (ψ := 77237/100000) 239 127
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t28 : ((-2103372999/16000000000 : ℚ) : ℝ) ≤ stT239 28 := by
  have hc : ((-1113/1600 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2103372999/16000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-1113/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c29 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((30381/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -590953/10000000) (δ := 11983/1000000000) (ψ := 77237/100000) 239 128
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t29 : ((902611001663/5000000000000 : ℚ) : ℝ) ≤ stT239 29 := by
  have hc : ((486071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((902611001663/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((486071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c30 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-2419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 395723/1000000) (δ := 479/40000000) (ψ := 77237/100000) 239 129
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t30 : ((-2217363659/1000000000000 : ℚ) : ℝ) ≤ stT239 30 := by
  have hc : ((-2429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2217363659/1000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-2429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c31 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-999987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490077/625000) (δ := 187/15625000) (ψ := 77237/100000) 239 130
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t31 : ((-898060226999/5000000000000 : ℚ) : ℝ) ≤ stT239 31 := by
  have hc : ((-1000037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898060226999/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-1000037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c32 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-33479/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2302423/5000000) (δ := 12049/1000000000) (ψ := 77237/100000) 239 132
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t32 : ((-236776479747/5000000000000 : ℚ) : ℝ) ≤ stT239 32 := by
  have hc : ((-133941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236776479747/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-133941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c33 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((143483/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1926779/10000000) (δ := 12147/1000000000) (ψ := 77237/100000) 239 133
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t33 : ((31219294381/250000000000 : ℚ) : ℝ) ≤ stT239 33 := by
  have hc : ((143473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31219294381/250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((143473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c34 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((249181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101213/5000000) (δ := 377/31250000) (ψ := 77237/100000) 239 134
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t34 : ((170928095989/1000000000000 : ℚ) : ℝ) ≤ stT239 34 := by
  have hc : ((498337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170928095989/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((498337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c35 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((74797/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 907247/5000000) (δ := 12071/1000000000) (ψ := 77237/100000) 239 135
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t35 : ((3950672373/31250000000 : ℚ) : ℝ) ≤ stT239 35 := by
  have hc : ((9349/12500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3950672373/31250000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((9349/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c36 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((385121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2938643/10000000) (δ := 481/40000000) (ψ := 77237/100000) 239 136
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t36 : ((320892371643/5000000000000 : ℚ) : ℝ) ≤ stT239 36 := by
  have hc : ((385071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320892371643/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((385071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c37 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((32449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1800791/5000000) (δ := 6059/500000000) (ψ := 77237/100000) 239 137
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t37 : ((106650498397/5000000000000 : ℚ) : ℝ) ≤ stT239 37 := by
  have hc : ((64873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106650498397/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((64873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c38 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((19819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3827869/10000000) (δ := 3023/250000000) (ψ := 77237/100000) 239 138
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t38 : ((8027525979/1250000000000 : ℚ) : ℝ) ≤ stT239 38 := by
  have hc : ((9897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8027525979/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((9897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c39 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((57219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3640267/10000000) (δ := 12099/1000000000) (ψ := 77237/100000) 239 139
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t39 : ((45791832757/2500000000000 : ℚ) : ℝ) ≤ stT239 39 := by
  have hc : ((28597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45791832757/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((28597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c40 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((85001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3059689/10000000) (δ := 12007/1000000000) (ψ := 77237/100000) 239 140
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t40 : ((134378546913/2500000000000 : ℚ) : ℝ) ≤ stT239 40 := by
  have hc : ((169977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134378546913/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((169977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c41 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((665807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1052777/5000000) (δ := 11989/1000000000) (ψ := 77237/100000) 239 141
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t41 : ((1039737339909/10000000000000 : ℚ) : ℝ) ≤ stT239 41 := by
  have hc : ((665757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1039737339909/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((665757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c42 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((949749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 795907/10000000) (δ := 12021/1000000000) (ψ := 77237/100000) 239 142
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t42 : ((1465416897067/10000000000000 : ℚ) : ℝ) ≤ stT239 42 := by
  have hc : ((949699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1465416897067/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((949699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c43 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((94241/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -852583/10000000) (δ := 483/40000000) (ψ := 77237/100000) 239 143
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t43 : ((7185424323/50000000000 : ℚ) : ℝ) ≤ stT239 43 := by
  have hc : ((23559/25000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7185424323/50000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((23559/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c44 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((213453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4413/15625) (δ := 3017/250000000) (ψ := 77237/100000) 239 144
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t44 : ((20109666373/312500000000 : ℚ) : ℝ) ≤ stT239 44 := by
  have hc : ((53357/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20109666373/312500000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((53357/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c45 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-226941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1020957/2000000) (δ := 299/25000000) (ψ := 77237/100000) 239 145
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t45 : ((-21146308737/312500000000 : ℚ) : ℝ) ≤ stT239 45 := by
  have hc : ((-113483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21146308737/312500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-113483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c46 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-997589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536071/2000000) (δ := 243/20000000) (ψ := 77237/100000) 239 146
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t46 : ((-73546944719/500000000000 : ℚ) : ℝ) ≤ stT239 46 := by
  have hc : ((-997639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73546944719/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-997639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c47 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-9537/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5169659/10000000) (δ := 241/20000000) (ψ := 77237/100000) 239 146
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t47 : ((-139126037/2000000000 : ℚ) : ℝ) ≤ stT239 47 := by
  have hc : ((-4769/10000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139126037/2000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-4769/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c48 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((684819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1020551/5000000) (δ := 11957/1000000000) (ψ := 77237/100000) 239 147
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t48 : ((7907027643/80000000000 : ℚ) : ℝ) ≤ stT239 48 := by
  have hc : ((684769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7907027643/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((684769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c49 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((214587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1346889/10000000) (δ := 377/31250000) (ψ := 77237/100000) 239 148
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t49 : ((613069816079/5000000000000 : ℚ) : ℝ) ≤ stT239 49 := by
  have hc : ((429149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((613069816079/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((429149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c50 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-205101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7787/15625) (δ := 3033/250000000) (ψ := 77237/100000) 239 149
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t50 : ((-72523015241/1250000000000 : ℚ) : ℝ) ≤ stT239 50 := by
  have hc : ((-102563/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72523015241/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-102563/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c51 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-184037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3424187/5000000) (δ := 11971/1000000000) (ψ := 77237/100000) 239 149
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t51 : ((-257717517207/2000000000000 : ℚ) : ℝ) ≤ stT239 51 := by
  have hc : ((-184047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257717517207/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-184047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c52 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((114047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109709/400000) (δ := 97/8000000) (ψ := 77237/100000) 239 150
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t52 : ((1265098743/20000000000 : ℚ) : ℝ) ≤ stT239 52 := by
  have hc : ((228069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1265098743/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((228069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c53 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((201479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -791969/5000000) (δ := 6043/500000000) (ψ := 77237/100000) 239 151
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t53 : ((110694156693/1000000000000 : ℚ) : ℝ) ≤ stT239 53 := by
  have hc : ((402933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110694156693/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((402933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c54 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-96227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1530843/2500000) (δ := 1201/100000000) (ψ := 77237/100000) 239 152
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t54 : ((-130956901131/1250000000000 : ℚ) : ℝ) ≤ stT239 54 := by
  have hc : ((-384933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130956901131/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-384933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c55 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-17861/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 968043/2000000) (δ := 1211/100000000) (ψ := 77237/100000) 239 152
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t55 : ((-120435717/2500000000 : ℚ) : ℝ) ≤ stT239 55 := by
  have hc : ((-35727/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120435717/2500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-35727/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c56 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((999173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50847/5000000) (δ := 3/250000) (ψ := 77237/100000) 239 153
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t56 : ((667567029819/5000000000000 : ℚ) : ℝ) ≤ stT239 56 := by
  have hc : ((999123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667567029819/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((999123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c57 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-249681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2617073/5000000) (δ := 12107/1000000000) (ψ := 77237/100000) 239 154
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t57 : ((-165371918649/2500000000000 : ℚ) : ℝ) ≤ stT239 57 := by
  have hc : ((-124853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165371918649/2500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-124853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c58 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-472553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2578727/5000000) (δ := 2999/250000000) (ψ := 77237/100000) 239 154
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t58 : ((-124111691639/2000000000000 : ℚ) : ℝ) ≤ stT239 58 := by
  have hc : ((-472603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124111691639/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-472603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c59 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((990949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67321/2000000) (δ := 6007/500000000) (ψ := 77237/100000) 239 155
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t59 : ((1290040508211/10000000000000 : ℚ) : ℝ) ≤ stT239 59 := by
  have hc : ((990899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1290040508211/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((990899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c60 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-369011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3001163/5000000) (δ := 6011/500000000) (ψ := 77237/100000) 239 156
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t60 : ((-23821181541/250000000000 : ℚ) : ℝ) ≤ stT239 60 := by
  have hc : ((-92259/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23821181541/250000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-92259/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c61 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((10611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3873931/10000000) (δ := 6061/500000000) (ψ := 77237/100000) 239 156
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t61 : ((423561739/156250000000 : ℚ) : ℝ) ≤ stT239 61 := by
  have hc : ((5293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((423561739/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((5293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c62 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((661969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132399/625000) (δ := 5987/500000000) (ψ := 77237/100000) 239 157
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t62 : ((840637791919/10000000000000 : ℚ) : ℝ) ≤ stT239 62 := by
  have hc : ((661919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((840637791919/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((661919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c63 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-986443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1488371/2000000) (δ := 5987/500000000) (ψ := 77237/100000) 239 157
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t63 : ((-621432386913/5000000000000 : ℚ) : ℝ) ≤ stT239 63 := by
  have hc : ((-986493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621432386913/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-986493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c64 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((224301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1143501/10000000) (δ := 11967/1000000000) (ψ := 77237/100000) 239 158
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t64 : ((448577/4000000 : ℚ) : ℝ) ≤ stT239 64 := by
  have hc : ((448577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448577/4000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((448577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c65 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-65281/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5300703/10000000) (δ := 603/50000000) (ψ := 77237/100000) 239 159
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t65 : ((-80978909963/1250000000000 : ℚ) : ℝ) ≤ stT239 65 := by
  have hc : ((-261149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80978909963/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-261149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c66 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((10533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3821629/10000000) (δ := 12143/1000000000) (ψ := 77237/100000) 239 159
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t66 : ((12949830737/2500000000000 : ℚ) : ℝ) ≤ stT239 66 := by
  have hc : ((21041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12949830737/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((21041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c67 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((398903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2901189/10000000) (δ := 243/20000000) (ψ := 77237/100000) 239 160
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t67 : ((243638158491/5000000000000 : ℚ) : ℝ) ≤ stT239 67 := by
  have hc : ((398853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243638158491/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((398853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c68 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-11312/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5950833/10000000) (δ := 241/20000000) (ψ := 77237/100000) 239 160
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t68 : ((-439000712111/5000000000000 : ℚ) : ℝ) ≤ stT239 68 := by
  have hc : ((-362009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439000712111/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-362009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c69 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((114453/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258587/2500000) (δ := 6073/500000000) (ψ := 77237/100000) 239 161
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t69 : ((275555271123/2500000000000 : ℚ) : ℝ) ≤ stT239 69 := by
  have hc : ((457787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((275555271123/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((457787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c70 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-993229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7562901/10000000) (δ := 12057/1000000000) (ψ := 77237/100000) 239 161
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t70 : ((-1187195865891/10000000000000 : ℚ) : ℝ) ≤ stT239 70 := by
  have hc : ((-993279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1187195865891/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-993279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c71 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((123911/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82559/2500000) (δ := 2393/200000000) (ψ := 77237/100000) 239 162
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t71 : ((588191212439/5000000000000 : ℚ) : ℝ) ≤ stT239 71 := by
  have hc : ((495619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588191212439/5000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((495619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c72 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-29531/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7020913/10000000) (δ := 2993/250000000) (ψ := 77237/100000) 239 163
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t72 : ((-34804479297/312500000000 : ℚ) : ℝ) ≤ stT239 72 := by
  have hc : ((-472521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34804479297/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-472521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c73 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((883163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152573/1250000) (δ := 1509/125000000) (ψ := 77237/100000) 239 163
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t73 : ((1033605169443/10000000000000 : ℚ) : ℝ) ≤ stT239 73 := by
  have hc : ((883113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033605169443/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((883113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c74 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-661/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3179017/5000000) (δ := 3031/250000000) (ψ := 77237/100000) 239 164
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t74 : ((-9605547451/100000000000 : ℚ) : ℝ) ≤ stT239 74 := by
  have hc : ((-8263/10000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9605547451/100000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-8263/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c75 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((393487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1662269/10000000) (δ := 12079/1000000000) (ψ := 77237/100000) 239 164
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t75 : ((2271652857/25000000000 : ℚ) : ℝ) ≤ stT239 75 := by
  have hc : ((196731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2271652857/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((196731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c76 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-154387/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766461/1250000) (δ := 12117/1000000000) (ψ := 77237/100000) 239 165
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t76 : ((-177105556363/2000000000000 : ℚ) : ℝ) ≤ stT239 76 := by
  have hc : ((-154397/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177105556363/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-154397/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c77 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((391427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419723/2500000) (δ := 12017/1000000000) (ψ := 77237/100000) 239 165
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t77 : ((44604367621/500000000000 : ℚ) : ℝ) ≤ stT239 77 := by
  have hc : ((195701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44604367621/500000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((195701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c78 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-817421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -631929/1000000) (δ := 1211/100000000) (ψ := 77237/100000) 239 166
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t78 : ((-462802214469/5000000000000 : ℚ) : ℝ) ≤ stT239 78 := by
  have hc : ((-817471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-462802214469/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-817471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c79 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((869353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1292263/10000000) (δ := 11993/1000000000) (ψ := 77237/100000) 239 166
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t79 : ((978041504361/10000000000000 : ℚ) : ℝ) ≤ stT239 79 := by
  have hc : ((869303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((978041504361/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((869303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c80 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-928053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6899867/10000000) (δ := 121/10000000) (ψ := 77237/100000) 239 167
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t80 : ((-518825354751/5000000000000 : ℚ) : ℝ) ≤ stT239 80 := by
  have hc : ((-928103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518825354751/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-928103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c81 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((978233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32661/625000) (δ := 12103/1000000000) (ψ := 77237/100000) 239 167
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t81 : ((1086869891313/10000000000000 : ℚ) : ℝ) ≤ stT239 81 := by
  have hc : ((978183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1086869891313/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((978183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c82 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7853961/10000000) (δ := 12003/1000000000) (ψ := 77237/100000) 239 167
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t82 : ((-5521856079/50000000000 : ℚ) : ℝ) ≤ stT239 82 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5521856079/50000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c83 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((485119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305733/5000000) (δ := 2419/200000000) (ψ := 77237/100000) 239 168
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t83 : ((133114887087/1250000000000 : ℚ) : ℝ) ≤ stT239 83 := by
  have hc : ((242547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133114887087/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((242547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c84 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-173177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1636071/2500000) (δ := 5977/250000000) (ψ := 77237/100000) 239 168
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t84 : ((-18896260383/200000000000 : ℚ) : ℝ) ≤ stT239 84 := by
  have hc : ((-173187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18896260383/200000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-173187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c85 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((334833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418519/2000000) (δ := 2423/200000000) (ψ := 77237/100000) 239 169
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t85 : ((11348442713/156250000000 : ℚ) : ℝ) ≤ stT239 85 := by
  have hc : ((41851/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11348442713/156250000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((41851/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c86 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-94471/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979153/2000000) (δ := 2423/200000000) (ψ := 77237/100000) 239 169
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t86 : ((-25471050897/625000000000 : ℚ) : ℝ) ≤ stT239 86 := by
  have hc : ((-188967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25471050897/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-188967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c87 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((2243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3904561/10000000) (δ := 11981/1000000000) (ψ := 77237/100000) 239 170
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t87 : ((298918227/312500000000 : ℚ) : ℝ) ≤ stT239 87 := by
  have hc : ((4461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298918227/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((4461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c88 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((48811/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2924087/10000000) (δ := 12081/1000000000) (ψ := 77237/100000) 239 170
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t88 : ((208104039657/5000000000000 : ℚ) : ℝ) ≤ stT239 88 := by
  have hc : ((195219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208104039657/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((195219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c89 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-186523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241297/400000) (δ := 6037/500000000) (ψ := 77237/100000) 239 171
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t89 : ((-197727256929/2500000000000 : ℚ) : ℝ) ≤ stT239 89 := by
  have hc : ((-373071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197727256929/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-373071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c90 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((967043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321811/5000000) (δ := 5987/500000000) (ψ := 77237/100000) 239 171
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t90 : ((254824896339/2500000000000 : ℚ) : ℝ) ≤ stT239 90 := by
  have hc : ((966993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254824896339/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((966993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c91 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-194113/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7245907/10000000) (δ := 12037/500000000) (ψ := 77237/100000) 239 171
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t91 : ((-40699245811/400000000000 : ℚ) : ℝ) ≤ stT239 91 := by
  have hc : ((-194123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40699245811/400000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-194123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c92 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((715973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482987/2500000) (δ := 1517/125000000) (ψ := 77237/100000) 239 172
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t92 : ((186600318489/2500000000000 : ℚ) : ℝ) ≤ stT239 92 := by
  have hc : ((715923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186600318489/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((715923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c93 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-9517/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1131891/2500000) (δ := 12067/1000000000) (ψ := 77237/100000) 239 172
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t93 : ((-1233843261/50000000000 : ℚ) : ℝ) ≤ stT239 93 := by
  have hc : ((-9519/40000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1233843261/50000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-9519/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c94 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-84593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4789957/10000000) (δ := 3011/250000000) (ψ := 77237/100000) 239 173
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t94 : ((-87263974021/2500000000000 : ℚ) : ℝ) ≤ stT239 94 := by
  have hc : ((-169211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87263974021/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-169211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c95 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((408923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95803/625000) (δ := 759/62500000) (ψ := 77237/100000) 239 173
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t95 : ((104880088061/1250000000000 : ℚ) : ℝ) ≤ stT239 95 := by
  have hc : ((204449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104880088061/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((204449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c96 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-999667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7789449/10000000) (δ := 12059/1000000000) (ψ := 77237/100000) 239 173
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t96 : ((-1020332164257/10000000000000 : ℚ) : ℝ) ≤ stT239 96 := by
  have hc : ((-999717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1020332164257/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-999717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c97 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((770803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1726741/10000000) (δ := 747/62500000) (ψ := 77237/100000) 239 174
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t97 : ((391290487769/5000000000000 : ℚ) : ℝ) ≤ stT239 97 := by
  have hc : ((770753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391290487769/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((770753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c98 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-188673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2200759/5000000) (δ := 12051/1000000000) (ψ := 77237/100000) 239 174
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t98 : ((-190639104619/10000000000000 : ℚ) : ℝ) ≤ stT239 98 := by
  have hc : ((-188723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190639104619/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-188723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c99 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-501523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5240387/10000000) (δ := 2429/200000000) (ψ := 77237/100000) 239 175
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t99 : ((-252049962387/5000000000000 : ℚ) : ℝ) ≤ stT239 99 := by
  have hc : ((-501573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252049962387/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-501573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c100 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((476793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191167/2500000) (δ := 6029/500000000) (ψ := 77237/100000) 239 175
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t100 : ((14898985101/156250000000 : ℚ) : ℝ) ≤ stT239 100 := by
  have hc : ((14899/15625 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14898985101/156250000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((14899/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c101 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-224281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419377/625000) (δ := 6029/500000000) (ψ := 77237/100000) 239 175
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t101 : ((-223180555653/2500000000000 : ℚ) : ℝ) ≤ stT239 101 := by
  have hc : ((-448587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223180555653/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-448587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c102 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((320563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1555591/5000000) (δ := 2413/200000000) (ψ := 77237/100000) 239 176
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t102 : ((317354985411/10000000000000 : ℚ) : ℝ) ≤ stT239 102 := by
  have hc : ((320513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317354985411/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((320513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c103 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((92987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2718087/10000000) (δ := 6069/500000000) (ψ := 77237/100000) 239 176
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t103 : ((91612934433/2000000000000 : ℚ) : ℝ) ≤ stT239 103 := by
  have hc : ((92977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91612934433/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((92977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c104 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-193541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7216891/10000000) (δ := 12131/1000000000) (ψ := 77237/100000) 239 177
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t104 : ((-189792433131/2000000000000 : ℚ) : ℝ) ≤ stT239 104 := by
  have hc : ((-193551/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189792433131/2000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-193551/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c105 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((12899/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -749557/5000000) (δ := 1509/125000000) (ψ := 77237/100000) 239 177
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t105 : ((4027958937/50000000000 : ℚ) : ℝ) ≤ stT239 105 := by
  have hc : ((412743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4027958937/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((412743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c106 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-3793/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4164409/10000000) (δ := 2993/250000000) (ψ := 77237/100000) 239 177
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t106 : ((-368603037/40000000000 : ℚ) : ℝ) ≤ stT239 106 := by
  have hc : ((-759/8000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368603037/40000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-759/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c107 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-71907/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5933149/10000000) (δ := 1503/125000000) (ψ := 77237/100000) 239 178
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t107 : ((-8689998893/125000000000 : ℚ) : ℝ) ≤ stT239 107 := by
  have hc : ((-8989/12500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8689998893/125000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-8989/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c108 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((988773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74993/2000000) (δ := 1503/125000000) (ψ := 77237/100000) 239 178
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t108 : ((3805594827/40000000000 : ℚ) : ℝ) ≤ stT239 108 := by
  have hc : ((988723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3805594827/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((988723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c109 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-463539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2565977/5000000) (δ := 12079/1000000000) (ψ := 77237/100000) 239 178
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t109 : ((-444038061103/10000000000000 : ℚ) : ℝ) ≤ stT239 109 := by
  have hc : ((-463589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444038061103/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-463589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c110 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-459063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5119341/10000000) (δ := 751/62500000) (ψ := 77237/100000) 239 179
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t110 : ((-437747258319/10000000000000 : ℚ) : ℝ) ≤ stT239 110 := by
  have hc : ((-459113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437747258319/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-459113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c111 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((993373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143987/5000000) (δ := 3029/250000000) (ψ := 77237/100000) 239 179
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t111 : ((942819478711/10000000000000 : ℚ) : ℝ) ≤ stT239 111 := by
  have hc : ((993323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((942819478711/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((993323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c112 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-158727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5646713/10000000) (δ := 11987/1000000000) (ψ := 77237/100000) 239 179
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t112 : ((-18749357303/312500000000 : ℚ) : ℝ) ≤ stT239 112 := by
  have hc : ((-317479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18749357303/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-317479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c113 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-323317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4750073/10000000) (δ := 12009/1000000000) (ψ := 77237/100000) 239 180
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t113 : ((-304198127607/10000000000000 : ℚ) : ℝ) ≤ stT239 113 := by
  have hc : ((-323367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304198127607/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-323367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c114 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((978917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 514261/10000000) (δ := 6047/500000000) (ψ := 77237/100000) 239 180
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t114 : ((183358429839/2000000000000 : ℚ) : ℝ) ≤ stT239 114 := by
  have hc : ((978867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183358429839/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((978867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c115 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-165271/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2866323/5000000) (δ := 12109/1000000000) (ψ := 77237/100000) 239 180
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t115 : ((-61651076067/1000000000000 : ℚ) : ℝ) ≤ stT239 115 := by
  have hc : ((-330567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61651076067/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-330567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c116 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-171481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2401081/5000000) (δ := 6001/500000000) (ψ := 77237/100000) 239 181
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t116 : ((-79619688181/2500000000000 : ℚ) : ℝ) ≤ stT239 116 := by
  have hc : ((-85753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79619688181/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-85753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c117 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((247869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326659/10000000) (δ := 12101/1000000000) (ψ := 77237/100000) 239 181
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t117 : ((916573337/10000000000 : ℚ) : ℝ) ≤ stT239 117 := by
  have hc : ((495713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((916573337/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((495713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c118 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-279809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2705901/5000000) (δ := 12001/1000000000) (ψ := 77237/100000) 239 181
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t118 : ((-5152163691/100000000000 : ℚ) : ℝ) ≤ stT239 118 := by
  have hc : ((-139917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5152163691/100000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-139917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c119 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-506219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2626989/5000000) (δ := 3027/250000000) (ψ := 77237/100000) 239 182
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t119 : ((-464096286031/10000000000000 : ℚ) : ℝ) ≤ stT239 119 := by
  have hc : ((-506269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464096286031/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-506269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c120 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((497423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253919/10000000) (δ := 1501/125000000) (ψ := 77237/100000) 239 182
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t120 : ((22702985613/250000000000 : ℚ) : ℝ) ≤ stT239 120 := by
  have hc : ((248699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22702985613/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((248699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c121 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-153029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2352307/5000000) (δ := 1501/125000000) (ψ := 77237/100000) 239 182
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t121 : ((-69570006957/2500000000000 : ℚ) : ℝ) ≤ stT239 121 := by
  have hc : ((-76527/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69570006957/2500000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-76527/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c122 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-190023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3042813/5000000) (δ := 1511/125000000) (ψ := 77237/100000) 239 183
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t122 : ((-172050160209/2500000000000 : ℚ) : ℝ) ≤ stT239 122 := by
  have hc : ((-380071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172050160209/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-380071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c123 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((885503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604027/5000000) (δ := 2997/250000000) (ψ := 77237/100000) 239 183
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t123 : ((798385521057/10000000000000 : ℚ) : ℝ) ≤ stT239 123 := by
  have hc : ((885453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((798385521057/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((885453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c124 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((29627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3630023/10000000) (δ := 2997/250000000) (ψ := 77237/100000) 239 183
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t124 : ((26594590977/2500000000000 : ℚ) : ℝ) ≤ stT239 124 := by
  have hc : ((59229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26594590977/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((59229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c125 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-973641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7278701/10000000) (δ := 151/12500000) (ψ := 77237/100000) 239 184
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t125 : ((-217724123437/2500000000000 : ℚ) : ℝ) ≤ stT239 125 := by
  have hc : ((-973691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217724123437/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-973691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c126 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((534331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2517701/10000000) (δ := 12023/1000000000) (ψ := 77237/100000) 239 184
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t126 : ((47597491447/1000000000000 : ℚ) : ℝ) ≤ stT239 126 := by
  have hc : ((534281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47597491447/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((534281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c127 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((19857/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 551399/2500000) (δ := 599/50000000) (ψ := 77237/100000) 239 184
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t127 : ((70475366393/1250000000000 : ℚ) : ℝ) ≤ stT239 127 := by
  have hc : ((317687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70475366393/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((317687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c128 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-463431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1722977/2500000) (δ := 599/50000000) (ψ := 77237/100000) 239 184
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t128 : ((-3200322993/39062500000 : ℚ) : ℝ) ≤ stT239 128 := by
  have hc : ((-14483/15625 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3200322993/39062500000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-14483/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c129 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-47767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4166191/10000000) (δ := 12073/1000000000) (ψ := 77237/100000) 239 185
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t129 : ((-2629907137/312500000000 : ℚ) : ℝ) ≤ stT239 129 := by
  have hc : ((-2987/31250 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2629907137/312500000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-2987/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c130 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((123001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55963/1250000) (δ := 12073/1000000000) (ψ := 77237/100000) 239 185
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t130 : ((215747058891/2500000000000 : ℚ) : ℝ) ≤ stT239 130 := by
  have hc : ((491979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215747058891/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((491979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c131 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-85137/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5026287/10000000) (δ := 11973/1000000000) (ψ := 77237/100000) 239 185
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t131 : ((-14878671927/400000000000 : ℚ) : ℝ) ≤ stT239 131 := by
  have hc : ((-85147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14878671927/400000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-85147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c132 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-773519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -767241/1250000) (δ := 6033/500000000) (ψ := 77237/100000) 239 186
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t132 : ((-673305948341/10000000000000 : ℚ) : ℝ) ≤ stT239 132 := by
  have hc : ((-773569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-673305948341/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-773569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c133 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((397621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -407119/2500000) (δ := 6033/500000000) (ψ := 77237/100000) 239 186
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t133 : ((86189767491/1250000000000 : ℚ) : ℝ) ≤ stT239 133 := by
  have hc : ((99399/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86189767491/1250000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((99399/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c134 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((52327/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711797/2500000) (δ := 24037/1000000000) (ψ := 77237/100000) 239 186
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t134 : ((45198221661/1250000000000 : ℚ) : ℝ) ≤ stT239 134 := by
  have hc : ((209283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45198221661/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((209283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c135 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-974623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 728957/1000000) (δ := 6033/500000000) (ψ := 77237/100000) 239 186
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t135 : ((-838864988199/10000000000000 : ℚ) : ℝ) ≤ stT239 135 := by
  have hc : ((-974673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-838864988199/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-974673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c136 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-32711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4008783/10000000) (δ := 3011/250000000) (ψ := 77237/100000) 239 187
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t136 : ((-28092328173/10000000000000 : ℚ) : ℝ) ≤ stT239 136 := by
  have hc : ((-32761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28092328173/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-32761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c137 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((989153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184281/5000000) (δ := 759/62500000) (ψ := 77237/100000) 239 187
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t137 : ((845047071771/10000000000000 : ℚ) : ℝ) ≤ stT239 137 := by
  have hc : ((989103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((845047071771/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((989103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c138 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-30963/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2357/5000) (δ := 3011/250000000) (ψ := 77237/100000) 239 187
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t138 : ((-3295215847/125000000000 : ℚ) : ℝ) ≤ stT239 138 := by
  have hc : ((-3871/12500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3295215847/125000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-3871/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c139 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-891723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3339917/5000000) (δ := 12051/1000000000) (ψ := 77237/100000) 239 188
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t139 : ((-756392049097/10000000000000 : ℚ) : ℝ) ≤ stT239 139 := by
  have hc : ((-891773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-756392049097/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-891773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c140 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((71827/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479331/2000000) (δ := 12151/1000000000) (ψ := 77237/100000) 239 188
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t140 : ((121399188291/2500000000000 : ℚ) : ℝ) ≤ stT239 140 := by
  have hc : ((287283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121399188291/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((287283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c141 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((736851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1855991/10000000) (δ := 747/62500000) (ψ := 77237/100000) 239 188
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t141 : ((620497698951/10000000000000 : ℚ) : ℝ) ≤ stT239 141 := by
  have hc : ((736801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((620497698951/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((736801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c142 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-379137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6078643/10000000) (δ := 747/62500000) (ψ := 77237/100000) 239 188
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t142 : ((-79546481371/1250000000000 : ℚ) : ℝ) ≤ stT239 142 := by
  have hc : ((-189581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79546481371/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-189581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c143 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-567713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339769/625000) (δ := 6029/500000000) (ψ := 77237/100000) 239 189
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t143 : ((-474787834409/10000000000000 : ℚ) : ℝ) ≤ stT239 143 := by
  have hc : ((-567763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474787834409/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-567763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c144 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((873219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636283/5000000) (δ := 2409/200000000) (ψ := 77237/100000) 239 189
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t144 : ((727640542277/10000000000000 : ℚ) : ℝ) ≤ stT239 144 := by
  have hc : ((873169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((727640542277/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((873169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c145 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((413071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2862433/10000000) (δ := 5979/500000000) (ψ := 77237/100000) 239 189
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t145 : ((171497470767/5000000000000 : ℚ) : ℝ) ≤ stT239 145 := by
  have hc : ((413021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171497470767/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((413021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c146 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-187599/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6968991/10000000) (δ := 6029/500000000) (ψ := 77237/100000) 239 189
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t146 : ((-77633167027/1000000000000 : ℚ) : ℝ) ≤ stT239 146 := by
  have hc : ((-187609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77633167027/1000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-187609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c147 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-289211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4660497/10000000) (δ := 6033/500000000) (ψ := 77237/100000) 239 190
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t147 : ((-238578712407/10000000000000 : ℚ) : ℝ) ≤ stT239 147 := by
  have hc : ((-289261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238578712407/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-289261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c148 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((194083/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -609627/10000000) (δ := 12137/1000000000) (ψ := 77237/100000) 239 190
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t148 : ((79763420781/1000000000000 : ℚ) : ℝ) ≤ stT239 148 := by
  have hc : ((194073/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79763420781/1000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((194073/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c149 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((2547/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1706999/5000000) (δ := 12037/1000000000) (ψ := 77237/100000) 239 190
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t149 : ((16688554701/1000000000000 : ℚ) : ℝ) ≤ stT239 149 := by
  have hc : ((20371/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16688554701/1000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((20371/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c150 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-196863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926327/1250000) (δ := 5983/500000000) (ψ := 77237/100000) 239 190
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t150 : ((-160746213881/2000000000000 : ℚ) : ℝ) ≤ stT239 150 := by
  have hc : ((-196873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160746213881/2000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-196873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c151 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-797/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4327199/10000000) (δ := 1203/100000000) (ψ := 77237/100000) 239 191
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t151 : ((-2595173121/200000000000 : ℚ) : ℝ) ≤ stT239 151 := by
  have hc : ((-3189/20000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2595173121/200000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-3189/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c152 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((988271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -383281/10000000) (δ := 1213/100000000) (ψ := 77237/100000) 239 191
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t152 : ((801552970647/10000000000000 : ℚ) : ℝ) ≤ stT239 152 := by
  have hc : ((988221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((801552970647/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((988221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c153 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((156247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1767383/5000000) (δ := 11973/1000000000) (ψ := 77237/100000) 239 191
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t153 : ((31569444261/2500000000000 : ℚ) : ℝ) ≤ stT239 153 := by
  have hc : ((156197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31569444261/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((156197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c154 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-985471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7427299/10000000) (δ := 1203/100000000) (ψ := 77237/100000) 239 191
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t154 : ((-794155488783/10000000000000 : ℚ) : ℝ) ≤ stT239 154 := by
  have hc : ((-985521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-794155488783/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-985521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c155 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-193317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -882669/2000000) (δ := 151/12500000) (ψ := 77237/100000) 239 192
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t155 : ((-7765812087/500000000000 : ℚ) : ℝ) ≤ stT239 155 := by
  have hc : ((-193367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7765812087/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-193367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c156 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((974041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570883/10000000) (δ := 12123/1000000000) (ψ := 77237/100000) 239 192
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t156 : ((1218462741/15625000000 : ℚ) : ℝ) ≤ stT239 156 := by
  have hc : ((973991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1218462741/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((973991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c157 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((134323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3247023/10000000) (δ := 599/50000000) (ψ := 77237/100000) 239 192
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t157 : ((26795338407/1250000000000 : ℚ) : ℝ) ≤ stT239 157 := by
  have hc : ((67149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26795338407/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((67149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c158 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-947547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 704067/1000000) (δ := 599/50000000) (ψ := 77237/100000) 239 192
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t158 : ((-376934187063/5000000000000 : ℚ) : ℝ) ≤ stT239 158 := by
  have hc : ((-947597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376934187063/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-947597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c159 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-378543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2448773/5000000) (δ := 12087/1000000000) (ψ := 77237/100000) 239 193
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t159 : ((-75060983959/2500000000000 : ℚ) : ℝ) ≤ stT239 159 := by
  have hc : ((-378593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75060983959/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-378593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c160 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((895793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57573/500000) (δ := 12087/1000000000) (ψ := 77237/100000) 239 193
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t160 : ((708146647767/10000000000000 : ℚ) : ℝ) ≤ stT239 160 := by
  have hc : ((895743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((708146647767/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((895743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c161 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((5161/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2571263/10000000) (δ := 3029/250000000) (ψ := 77237/100000) 239 193
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t161 : ((813408331/20000000000 : ℚ) : ℝ) ≤ stT239 161 := by
  have hc : ((10321/20000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((813408331/20000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((10321/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c162 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-403069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6270983/10000000) (δ := 3029/250000000) (ψ := 77237/100000) 239 193
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t162 : ((-6334017569/100000000000 : ℚ) : ℝ) ≤ stT239 162 := by
  have hc : ((-201547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6334017569/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-201547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c163 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-669261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -230401/400000) (δ := 12109/1000000000) (ψ := 77237/100000) 239 194
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t163 : ((-524245203171/10000000000000 : ℚ) : ℝ) ≤ stT239 163 := by
  have hc : ((-669311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-524245203171/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-669311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c164 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((133159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421119/2000000) (δ := 5997/500000000) (ψ := 77237/100000) 239 194
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t164 : ((25992948333/500000000000 : ℚ) : ℝ) ≤ stT239 164 := by
  have hc : ((133149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25992948333/500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((133149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c165 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((10241/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1526607/10000000) (δ := 12109/1000000000) (ψ := 77237/100000) 239 194
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t165 : ((31888445827/500000000000 : ℚ) : ℝ) ≤ stT239 165 := by
  have hc : ((81923/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31888445827/500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((81923/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c166 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-93057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2568441/5000000) (δ := 6047/500000000) (ψ := 77237/100000) 239 194
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t166 : ((-72234045117/2000000000000 : ℚ) : ℝ) ≤ stT239 166 := by
  have hc : ((-93067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72234045117/2000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-93067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c167 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-469923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6982437/10000000) (δ := 12001/1000000000) (ψ := 77237/100000) 239 195
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t167 : ((-1420535317/19531250000 : ℚ) : ℝ) ≤ stT239 167 := by
  have hc : ((-117487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1420535317/19531250000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-117487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c168 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((203249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1707651/5000000) (δ := 6001/500000000) (ψ := 77237/100000) 239 195
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t168 : ((39192819921/2500000000000 : ℚ) : ℝ) ≤ stT239 168 := by
  have hc : ((203199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39192819921/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((203199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c169 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((998633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130741/10000000) (δ := 6001/500000000) (ψ := 77237/100000) 239 195
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t169 : ((76814000109/1000000000000 : ℚ) : ℝ) ≤ stT239 169 := by
  have hc : ((998583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76814000109/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((998583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c170 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((108259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 913953/2500000) (δ := 6051/500000000) (ψ := 77237/100000) 239 195
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t170 : ((20748101869/2500000000000 : ℚ) : ℝ) ≤ stT239 170 := by
  have hc : ((108209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20748101869/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((108209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c171 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-961741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7160209/10000000) (δ := 6001/500000000) (ψ := 77237/100000) 239 195
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t171 : ((-9193760169/125000000000 : ℚ) : ℝ) ≤ stT239 171 := by
  have hc : ((-961791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9193760169/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-961791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c172 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-439211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316487/625000) (δ := 6047/500000000) (ψ := 77237/100000) 239 196
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t172 : ((-334933437673/10000000000000 : ℚ) : ℝ) ≤ stT239 172 := by
  have hc : ((-439261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334933437673/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-439261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c173 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((80209/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200003/1250000) (δ := 12109/1000000000) (ψ := 77237/100000) 239 196
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t173 : ((3048894907/50000000000 : ℚ) : ℝ) ≤ stT239 173 := by
  have hc : ((20051/25000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3048894907/50000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((20051/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c174 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((370071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 921893/5000000) (δ := 6047/500000000) (ψ := 77237/100000) 239 196
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t174 : ((70132783127/1250000000000 : ℚ) : ℝ) ≤ stT239 174 := by
  have hc : ((185023/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70132783127/1250000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((185023/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c175 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-511007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131697/250000) (δ := 12109/1000000000) (ψ := 77237/100000) 239 196
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t175 : ((-386322806953/10000000000000 : ℚ) : ℝ) ≤ stT239 175 := by
  have hc : ((-511057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386322806953/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-511057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c176 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-118361/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7035529/10000000) (δ := 12087/1000000000) (ψ := 77237/100000) 239 197
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t176 : ((-356890989351/5000000000000 : ℚ) : ℝ) ≤ stT239 176 := by
  have hc : ((-473469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356890989351/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-473469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c177 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((22097/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3650213/10000000) (δ := 751/62500000) (ψ := 77237/100000) 239 197
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t177 : ((8300802601/1000000000000 : ℚ) : ℝ) ≤ stT239 177 := by
  have hc : ((22087/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8300802601/1000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((22087/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c178 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((496777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142009/5000000) (δ := 12087/1000000000) (ψ := 77237/100000) 239 197
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t178 : ((23270688957/312500000000 : ℚ) : ℝ) ≤ stT239 178 := by
  have hc : ((31047/31250 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23270688957/312500000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((31047/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c179 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((338623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3063357/10000000) (δ := 3029/250000000) (ψ := 77237/100000) 239 197
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t179 : ((50612262051/2000000000000 : ℚ) : ℝ) ≤ stT239 179 := by
  have hc : ((338573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50612262051/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((338573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c180 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-833833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6392029/10000000) (δ := 11987/1000000000) (ψ := 77237/100000) 239 197
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t180 : ((-155384924337/2500000000000 : ℚ) : ℝ) ≤ stT239 180 := by
  have hc : ((-833883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155384924337/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-833883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c181 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-369461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1201133/2000000) (δ := 151/12500000) (ψ := 77237/100000) 239 198
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t181 : ((-27463709637/500000000000 : ℚ) : ℝ) ≤ stT239 181 := by
  have hc : ((-184743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27463709637/500000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-184743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c182 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((7289/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2713679/10000000) (δ := 151/12500000) (ψ := 77237/100000) 239 198
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t182 : ((172876315527/5000000000000 : ℚ) : ℝ) ≤ stT239 182 := by
  have hc : ((233223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172876315527/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((233223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c183 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((243747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 560323/10000000) (δ := 12123/1000000000) (ψ := 77237/100000) 239 198
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t183 : ((360347321649/5000000000000 : ℚ) : ℝ) ≤ stT239 183 := by
  have hc : ((487469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360347321649/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((487469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c184 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((22099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3816459/10000000) (δ := 12123/1000000000) (ψ := 77237/100000) 239 198
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t184 : ((8136575733/2500000000000 : ℚ) : ℝ) ≤ stT239 184 := by
  have hc : ((11037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8136575733/2500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((11037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c185 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-949359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881871/1250000) (δ := 151/12500000) (ψ := 77237/100000) 239 198
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t185 : ((-139603947587/2000000000000 : ℚ) : ℝ) ≤ stT239 185 := by
  have hc : ((-949409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139603947587/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-949409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c186 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-141573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678999/1250000) (δ := 11973/1000000000) (ψ := 77237/100000) 239 199
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t186 : ((-51907792839/1250000000000 : ℚ) : ℝ) ≤ stT239 186 := by
  have hc : ((-283171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51907792839/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-283171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c187 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((314209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2228197/10000000) (δ := 11973/1000000000) (ψ := 77237/100000) 239 199
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t187 : ((3589905657/78125000000 : ℚ) : ℝ) ≤ stT239 187 := by
  have hc : ((39273/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3589905657/78125000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((39273/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c188 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((463703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19169/200000) (δ := 1203/100000000) (ψ := 77237/100000) 239 199
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t188 : ((42271436709/625000000000 : ℚ) : ℝ) ≤ stT239 188 := by
  have hc : ((231839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42271436709/625000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((231839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c189 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-2513/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4128247/10000000) (δ := 11973/1000000000) (ψ := 77237/100000) 239 199
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t189 : ((-29265202569/5000000000000 : ℚ) : ℝ) ≤ stT239 189 := by
  have hc : ((-40233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29265202569/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-40233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c190 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-973873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1456251/2000000) (δ := 1213/100000000) (ψ := 77237/100000) 239 199
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t190 : ((-706558736271/10000000000000 : ℚ) : ℝ) ≤ stT239 190 := by
  have hc : ((-973923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-706558736271/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-973923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c191 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-259329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330637/625000) (δ := 12037/1000000000) (ψ := 77237/100000) 239 200
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t191 : ((-3753241411/100000000000 : ℚ) : ℝ) ≤ stT239 191 := by
  have hc : ((-129677/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3753241411/100000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-129677/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c192 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((646321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2170107/10000000) (δ := 5983/500000000) (ψ := 77237/100000) 239 200
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t192 : ((466405379177/10000000000000 : ℚ) : ℝ) ≤ stT239 192 := by
  have hc : ((646271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466405379177/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((646271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c193 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((931051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 466893/5000000) (δ := 5983/500000000) (ψ := 77237/100000) 239 200
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t193 : ((134029696963/2000000000000 : ℚ) : ℝ) ≤ stT239 193 := by
  have hc : ((931001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134029696963/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((931001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c194 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-37861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2010833/5000000) (δ := 5983/500000000) (ψ := 77237/100000) 239 200
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t194 : ((-27218543649/10000000000000 : ℚ) : ℝ) ≤ stT239 194 := by
  have hc : ((-37911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27218543649/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-37911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c195 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-954107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7093653/10000000) (δ := 12137/1000000000) (ψ := 77237/100000) 239 200
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t195 : ((-136657228011/2000000000000 : ℚ) : ℝ) ≤ stT239 195 := by
  have hc : ((-954157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136657228011/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-954157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c196 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-60711/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2779019/5000000) (δ := 2429/200000000) (ψ := 77237/100000) 239 201
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t196 : ((-5421073597/125000000000 : ℚ) : ℝ) ≤ stT239 196 := by
  have hc : ((-15179/25000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5421073597/125000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-15179/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c197 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((267233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2517301/10000000) (δ := 2409/200000000) (ψ := 77237/100000) 239 201
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t197 : ((2379721047/62500000000 : ℚ) : ℝ) ≤ stT239 197 := by
  have hc : ((33401/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2379721047/62500000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((33401/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c198 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((30607/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508021/10000000) (δ := 2429/200000000) (ψ := 77237/100000) 239 201
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t198 : ((348005370603/5000000000000 : ℚ) : ℝ) ≤ stT239 198 := by
  have hc : ((489687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348005370603/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((489687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c199 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((81413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1759053/5000000) (δ := 5979/500000000) (ψ := 77237/100000) 239 201
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t199 : ((14423601707/1250000000000 : ℚ) : ℝ) ≤ stT239 199 := by
  have hc : ((20347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14423601707/1250000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((20347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c200 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-859573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260523/400000) (δ := 2409/200000000) (ψ := 77237/100000) 239 201
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t200 : ((-607845440661/10000000000000 : ℚ) : ℝ) ≤ stT239 200 := by
  have hc : ((-859623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-607845440661/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-859623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c201 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-396319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3107399/5000000) (δ := 12151/1000000000) (ψ := 77237/100000) 239 202
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t201 : ((-17472478439/312500000000 : ℚ) : ℝ) ≤ stT239 201 := by
  have hc : ((-49543/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17472478439/312500000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-49543/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c202 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((267659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203099/625000) (δ := 3013/250000000) (ψ := 77237/100000) 239 202
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t202 : ((188288889573/10000000000000 : ℚ) : ℝ) ≤ stT239 202 := by
  have hc : ((267609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188288889573/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((267609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c203 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((992859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5979/200000) (δ := 747/62500000) (ψ := 77237/100000) 239 202
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t203 : ((348407455179/5000000000000 : ℚ) : ℝ) ≤ stT239 203 := by
  have hc : ((992809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348407455179/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((992809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c204 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((15417/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527433/2000000) (δ := 747/62500000) (ψ := 77237/100000) 239 202
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t204 : ((8634371529/250000000000 : ℚ) : ℝ) ≤ stT239 204 := by
  have hc : ((246647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8634371529/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((246647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c205 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-607397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 277947/500000) (δ := 747/62500000) (ψ := 77237/100000) 239 202
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t205 : ((-424259815657/10000000000000 : ℚ) : ℝ) ≤ stT239 205 := by
  have hc : ((-607447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424259815657/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-607447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c206 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-121267/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7241469/10000000) (δ := 3011/250000000) (ψ := 77237/100000) 239 203
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t206 : ((-168990393131/2500000000000 : ℚ) : ℝ) ≤ stT239 206 := by
  have hc : ((-485093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168990393131/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-485093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c207 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-33523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869603/2000000) (δ := 12059/1000000000) (ψ := 77237/100000) 239 203
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t207 : ((-23307078117/2000000000000 : ℚ) : ℝ) ≤ stT239 207 := by
  have hc : ((-33533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23307078117/2000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-33533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c208 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((208097/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367121/2500000) (δ := 759/62500000) (ψ := 77237/100000) 239 203
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t208 : ((2308489443/40000000000 : ℚ) : ℝ) ≤ stT239 208 := by
  have hc : ((416169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2308489443/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((416169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c209 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((5299/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 698623/5000000) (δ := 11959/1000000000) (ψ := 77237/100000) 239 203
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t209 : ((29321410603/500000000000 : ℚ) : ℝ) ≤ stT239 209 := by
  have hc : ((84779/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29321410603/500000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((84779/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c210 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-32141/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4249293/10000000) (δ := 12059/1000000000) (ψ := 77237/100000) 239 203
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t210 : ((-22188037131/2500000000000 : ℚ) : ℝ) ≤ stT239 210 := by
  have hc : ((-64307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22188037131/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-64307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c211 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-953401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221493/312500) (δ := 3011/250000000) (ψ := 77237/100000) 239 203
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t211 : ((-656383318479/10000000000000 : ℚ) : ℝ) ≤ stT239 211 := by
  have hc : ((-953451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-656383318479/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-953451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c212 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-679633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5795147/10000000) (δ := 6033/500000000) (ψ := 77237/100000) 239 204
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t212 : ((-466808323449/10000000000000 : ℚ) : ℝ) ≤ stT239 212 := by
  have hc : ((-679683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-466808323449/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-679683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c213 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((368549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -745843/2500000) (δ := 5983/500000000) (ψ := 77237/100000) 239 204
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t213 : ((63122773203/2500000000000 : ℚ) : ℝ) ≤ stT239 213 := by
  have hc : ((368499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63122773203/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((368499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c214 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((997271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92371/5000000) (δ := 12037/1000000000) (ψ := 77237/100000) 239 204
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t214 : ((136337063457/2000000000000 : ℚ) : ℝ) ≤ stT239 214 := by
  have hc : ((997221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136337063457/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((997221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c215 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((505943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2600803/10000000) (δ := 12037/1000000000) (ψ := 77237/100000) 239 204
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t215 : ((172507995321/5000000000000 : ℚ) : ℝ) ≤ stT239 215 := by
  have hc : ((505893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172507995321/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((505893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c216 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-136709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2686721/5000000) (δ := 12037/1000000000) (ψ := 77237/100000) 239 204
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t216 : ((-93027222701/2500000000000 : ℚ) : ℝ) ≤ stT239 216 := by
  have hc : ((-273443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93027222701/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-273443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c217 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-124221/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -946841/1250000) (δ := 12073/1000000000) (ψ := 77237/100000) 239 205
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t217 : ((-67464838021/1000000000000 : ℚ) : ℝ) ≤ stT239 217 := by
  have hc : ((-496909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67464838021/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-496909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c218 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-352503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4827603/10000000) (δ := 1213/100000000) (ψ := 77237/100000) 239 205
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t218 : ((-119389605579/5000000000000 : ℚ) : ℝ) ≤ stT239 218 := by
  have hc : ((-352553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119389605579/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-352553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c219 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((334769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65407/312500) (δ := 12073/1000000000) (ψ := 77237/100000) 239 205
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t219 : ((28274863291/625000000000 : ℚ) : ℝ) ≤ stT239 219 := by
  have hc : ((41843/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28274863291/625000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((41843/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c220 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((968509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314533/5000000) (δ := 1203/100000000) (ψ := 77237/100000) 239 205
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t220 : ((652934089341/10000000000000 : ℚ) : ℝ) ≤ stT239 220 := by
  have hc : ((968459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((652934089341/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((968459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c221 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((233093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104339/312500) (δ := 1203/100000000) (ψ := 77237/100000) 239 205
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t221 : ((4898796903/312500000000 : ℚ) : ℝ) ≤ stT239 221 := by
  have hc : ((233043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4898796903/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((233043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c222 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-747129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3018161/5000000) (δ := 12073/1000000000) (ψ := 77237/100000) 239 205
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t222 : ((-501474416103/10000000000000 : ℚ) : ℝ) ≤ stT239 222 := by
  have hc : ((-747179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501474416103/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-747179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c223 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-235091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3493119/5000000) (δ := 12123/1000000000) (ψ := 77237/100000) 239 206
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t223 : ((-6297482351/100000000000 : ℚ) : ℝ) ≤ stT239 223 := by
  have hc : ((-470207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6297482351/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-470207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c224 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-153729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4312843/10000000) (δ := 151/12500000) (ψ := 77237/100000) 239 206
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t224 : ((-51374026983/5000000000000 : ℚ) : ℝ) ≤ stT239 224 := by
  have hc : ((-153779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51374026983/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-153779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c225 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((24677/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1651339/10000000) (δ := 151/12500000) (ψ := 77237/100000) 239 206
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t225 : ((131602201731/2500000000000 : ℚ) : ℝ) ≤ stT239 225 := by
  have hc : ((394807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131602201731/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((394807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c226 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((36853/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31197/312500) (δ := 24023/1000000000) (ψ := 77237/100000) 239 206
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t226 : ((2451291669/40000000000 : ℚ) : ℝ) ≤ stT239 226 := by
  have hc : ((36851/40000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2451291669/40000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((36851/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c227 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((7251/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3636297/10000000) (δ := 151/12500000) (ψ := 77237/100000) 239 206
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t227 : ((38484650709/5000000000000 : ℚ) : ℝ) ≤ stT239 227 := by
  have hc : ((57983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38484650709/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((57983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c228 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-402083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1565667/2500000) (δ := 151/12500000) (ψ := 77237/100000) 239 206
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t228 : ((-66575714709/1250000000000 : ℚ) : ℝ) ≤ stT239 228 := by
  have hc : ((-100527/125000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66575714709/1250000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-100527/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c229 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-458673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6830397/10000000) (δ := 2423/200000000) (ψ := 77237/100000) 239 207
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t229 : ((-151558176831/2500000000000 : ℚ) : ℝ) ≤ stT239 229 := by
  have hc : ((-229349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151558176831/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-229349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c230 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-374/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -422691/1000000) (δ := 2403/200000000) (ψ := 77237/100000) 239 207
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t230 : ((-7894768713/1000000000000 : ℚ) : ℝ) ≤ stT239 230 := by
  have hc : ((-11973/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7894768713/1000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-11973/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c231 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((396863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408679/2500000) (δ := 2403/200000000) (ψ := 77237/100000) 239 207
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t231 : ((130549979469/2500000000000 : ℚ) : ℝ) ≤ stT239 231 := by
  have hc : ((198419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130549979469/2500000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((198419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c232 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((929221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189249/2000000) (δ := 2403/200000000) (ψ := 77237/100000) 239 207
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t232 : ((152507623743/2500000000000 : ℚ) : ℝ) ≤ stT239 232 := by
  have hc : ((929171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152507623743/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((929171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c233 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((163597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 439519/1250000) (δ := 2423/200000000) (ψ := 77237/100000) 239 207
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t233 : ((107143074187/10000000000000 : ℚ) : ℝ) ≤ stT239 233 := by
  have hc : ((163547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107143074187/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((163547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c234 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-37867/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3037533/5000000) (δ := 1511/125000000) (ψ := 77237/100000) 239 207
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t234 : ((-49512174819/1000000000000 : ℚ) : ℝ) ≤ stT239 234 := by
  have hc : ((-75739/100000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49512174819/1000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-75739/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c235 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-190611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7084919/10000000) (δ := 3027/250000000) (ψ := 77237/100000) 239 208
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t235 : ((-124347606309/2000000000000 : ℚ) : ℝ) ≤ stT239 235 := by
  have hc : ((-190621/200000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124347606309/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-190621/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c236 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-122881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2273877/5000000) (δ := 2419/200000000) (ψ := 77237/100000) 239 208
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t236 : ((-8000504617/500000000000 : ℚ) : ℝ) ≤ stT239 236 := by
  have hc : ((-61453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8000504617/500000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-61453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c237 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((690557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404269/2000000) (δ := 2399/200000000) (ψ := 77237/100000) 239 208
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t237 : ((448531941483/10000000000000 : ℚ) : ℝ) ≤ stT239 237 := by
  have hc : ((690507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448531941483/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((690507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c238 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((980507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 494429/10000000) (δ := 2419/200000000) (ψ := 77237/100000) 239 208
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t238 : ((635535168771/10000000000000 : ℚ) : ℝ) ≤ stT239 238 := by
  have hc : ((980457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635535168771/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((980457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c239 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((14499/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1499843/5000000) (δ := 3027/250000000) (ψ := 77237/100000) 239 208
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t239 : ((4688663231/200000000000 : ℚ) : ℝ) ≤ stT239 239 := by
  have hc : ((14497/40000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4688663231/200000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((14497/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c240 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-586717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 686811/1250000) (δ := 2399/200000000) (ψ := 77237/100000) 239 208
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t240 : ((-189378462483/5000000000000 : ℚ) : ℝ) ≤ stT239 240 := by
  have hc : ((-586767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189378462483/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-586767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c241 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-31211/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772907/1000000) (δ := 6051/500000000) (ψ := 77237/100000) 239 209
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t241 : ((-321692649957/5000000000000 : ℚ) : ℝ) ≤ stT239 241 := by
  have hc : ((-499401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321692649957/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-499401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c242 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-63319/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2627471/5000000) (δ := 6051/500000000) (ψ := 77237/100000) 239 209
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t242 : ((-6513128613/200000000000 : ℚ) : ℝ) ≤ stT239 242 := by
  have hc : ((-253301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6513128613/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-253301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c243 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((109727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -348879/1250000) (δ := 12101/1000000000) (ψ := 77237/100000) 239 209
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t243 : ((281527407/10000000000 : ℚ) : ℝ) ≤ stT239 243 := by
  have hc : ((219429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281527407/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((219429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c244 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((247729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337219/10000000) (δ := 12101/1000000000) (ψ := 77237/100000) 239 209
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t244 : ((39646034959/625000000000 : ℚ) : ℝ) ≤ stT239 244 := by
  have hc : ((495433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39646034959/625000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((495433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c245 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((665517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1053263/5000000) (δ := 24101/1000000000) (ψ := 77237/100000) 239 209
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t245 : ((106287723773/2500000000000 : ℚ) : ℝ) ≤ stT239 245 := by
  have hc : ((665467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106287723773/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((665467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c246 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-242891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4540353/10000000) (δ := 12001/1000000000) (ψ := 77237/100000) 239 209
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t246 : ((-154893593957/10000000000000 : ℚ) : ℝ) ≤ stT239 246 := by
  have hc : ((-242941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154893593957/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-242941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c247 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-468671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6964291/10000000) (δ := 12001/1000000000) (ψ := 77237/100000) 239 209
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t247 : ((-7455605859/125000000000 : ℚ) : ℝ) ≤ stT239 247 := by
  have hc : ((-58587/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7455605859/125000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-58587/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c248 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-409887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6329533/10000000) (δ := 12009/1000000000) (ψ := 77237/100000) 239 210
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t248 : ((-32536816239/625000000000 : ℚ) : ℝ) ≤ stT239 248 := by
  have hc : ((-51239/62500 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32536816239/625000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-51239/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c249 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3925133/10000000) (δ := 12109/1000000000) (ψ := 77237/100000) 239 210
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t249 : ((109792683/2500000000000 : ℚ) : ℝ) ≤ stT239 249 := by
  have hc : ((693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109792683/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_c250 :
    |Real.cos (((239 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((818433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -765147/5000000) (δ := 6047/500000000) (ψ := 77237/100000) 239 210
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st239_t250 : ((103518084053/2000000000000 : ℚ) : ℝ) ≤ stT239 250 := by
  have hc : ((818383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((239 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((77237/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st239_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103518084053/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((818383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st239_p1 : ((716209/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT239 (i+1) := by
  rw [Finset.sum_range_one]
  exact st239_t1

theorem st239_p2 : ((933932915423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT239 (i+1))
      = (∑ i ∈ Finset.range 1, stT239 (i+1)) + stT239 2 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 1
    simpa using h
  have hprev := st239_p1
  have hstep := st239_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p3 : ((456728739133/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT239 (i+1))
      = (∑ i ∈ Finset.range 2, stT239 (i+1)) + stT239 3 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 2
    simpa using h
  have hprev := st239_p2
  have hstep := st239_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p4 : ((694151616703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT239 (i+1))
      = (∑ i ∈ Finset.range 3, stT239 (i+1)) + stT239 4 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 3
    simpa using h
  have hprev := st239_p3
  have hstep := st239_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p5 : ((2181037998029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT239 (i+1))
      = (∑ i ∈ Finset.range 4, stT239 (i+1)) + stT239 5 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 4
    simpa using h
  have hprev := st239_p4
  have hstep := st239_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p6 : ((4180862218139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT239 (i+1))
      = (∑ i ∈ Finset.range 5, stT239 (i+1)) + stT239 6 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 5
    simpa using h
  have hprev := st239_p5
  have hstep := st239_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p7 : ((5678846634837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT239 (i+1))
      = (∑ i ∈ Finset.range 6, stT239 (i+1)) + stT239 7 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 6
    simpa using h
  have hprev := st239_p6
  have hstep := st239_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p8 : ((7424650403841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT239 (i+1))
      = (∑ i ∈ Finset.range 7, stT239 (i+1)) + stT239 8 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 7
    simpa using h
  have hprev := st239_p7
  have hstep := st239_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p9 : ((2911790875147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT239 (i+1))
      = (∑ i ∈ Finset.range 8, stT239 (i+1)) + stT239 9 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 8
    simpa using h
  have hprev := st239_p8
  have hstep := st239_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p10 : ((4285182518603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT239 (i+1))
      = (∑ i ∈ Finset.range 9, stT239 (i+1)) + stT239 10 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 9
    simpa using h
  have hprev := st239_p9
  have hstep := st239_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p11 : ((5566593483151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT239 (i+1))
      = (∑ i ∈ Finset.range 10, stT239 (i+1)) + stT239 11 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 10
    simpa using h
  have hprev := st239_p10
  have hstep := st239_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p12 : ((4409392755919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT239 (i+1))
      = (∑ i ∈ Finset.range 11, stT239 (i+1)) + stT239 12 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 11
    simpa using h
  have hprev := st239_p11
  have hstep := st239_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p13 : ((3111488586953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT239 (i+1))
      = (∑ i ∈ Finset.range 12, stT239 (i+1)) + stT239 13 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 12
    simpa using h
  have hprev := st239_p12
  have hstep := st239_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p14 : ((6027889787971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT239 (i+1))
      = (∑ i ∈ Finset.range 13, stT239 (i+1)) + stT239 14 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 13
    simpa using h
  have hprev := st239_p13
  have hstep := st239_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p15 : ((7974951446843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT239 (i+1))
      = (∑ i ∈ Finset.range 14, stT239 (i+1)) + stT239 15 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 14
    simpa using h
  have hprev := st239_p14
  have hstep := st239_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p16 : ((3311729203123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT239 (i+1))
      = (∑ i ∈ Finset.range 15, stT239 (i+1)) + stT239 16 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 15
    simpa using h
  have hprev := st239_p15
  have hstep := st239_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p17 : ((5160189595649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT239 (i+1))
      = (∑ i ∈ Finset.range 16, stT239 (i+1)) + stT239 17 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 16
    simpa using h
  have hprev := st239_p16
  have hstep := st239_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p18 : ((6178691800157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT239 (i+1))
      = (∑ i ∈ Finset.range 17, stT239 (i+1)) + stT239 18 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 17
    simpa using h
  have hprev := st239_p17
  have hstep := st239_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p19 : ((7828424687171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT239 (i+1))
      = (∑ i ∈ Finset.range 18, stT239 (i+1)) + stT239 19 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 18
    simpa using h
  have hprev := st239_p18
  have hstep := st239_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p20 : ((8891124473189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT239 (i+1))
      = (∑ i ∈ Finset.range 19, stT239 (i+1)) + stT239 20 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 19
    simpa using h
  have hprev := st239_p19
  have hstep := st239_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p21 : ((1604154221551/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT239 (i+1))
      = (∑ i ∈ Finset.range 20, stT239 (i+1)) + stT239 21 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 20
    simpa using h
  have hprev := st239_p20
  have hstep := st239_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p22 : ((5976162643707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT239 (i+1))
      = (∑ i ∈ Finset.range 21, stT239 (i+1)) + stT239 22 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 21
    simpa using h
  have hprev := st239_p21
  have hstep := st239_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p23 : ((7253000572107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT239 (i+1))
      = (∑ i ∈ Finset.range 22, stT239 (i+1)) + stT239 23 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 22
    simpa using h
  have hprev := st239_p22
  have hstep := st239_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p24 : ((3716019930729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT239 (i+1))
      = (∑ i ∈ Finset.range 23, stT239 (i+1)) + stT239 24 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 23
    simpa using h
  have hprev := st239_p23
  have hstep := st239_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p25 : ((3308615727027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT239 (i+1))
      = (∑ i ∈ Finset.range 24, stT239 (i+1)) + stT239 25 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 24
    simpa using h
  have hprev := st239_p24
  have hstep := st239_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p26 : ((3661809056161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT239 (i+1))
      = (∑ i ∈ Finset.range 25, stT239 (i+1)) + stT239 26 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 25
    simpa using h
  have hprev := st239_p25
  have hstep := st239_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p27 : ((3696705052411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT239 (i+1))
      = (∑ i ∈ Finset.range 26, stT239 (i+1)) + stT239 27 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 26
    simpa using h
  have hprev := st239_p26
  have hstep := st239_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p28 : ((6078801980447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT239 (i+1))
      = (∑ i ∈ Finset.range 27, stT239 (i+1)) + stT239 28 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 27
    simpa using h
  have hprev := st239_p27
  have hstep := st239_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p29 : ((7884023983773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT239 (i+1))
      = (∑ i ∈ Finset.range 28, stT239 (i+1)) + stT239 29 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 28
    simpa using h
  have hprev := st239_p28
  have hstep := st239_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p30 : ((7861850347183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT239 (i+1))
      = (∑ i ∈ Finset.range 29, stT239 (i+1)) + stT239 30 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 29
    simpa using h
  have hprev := st239_p29
  have hstep := st239_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p31 : ((1213145978637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT239 (i+1))
      = (∑ i ∈ Finset.range 30, stT239 (i+1)) + stT239 31 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 30
    simpa using h
  have hprev := st239_p30
  have hstep := st239_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p32 : ((5592176933691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT239 (i+1))
      = (∑ i ∈ Finset.range 31, stT239 (i+1)) + stT239 32 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 31
    simpa using h
  have hprev := st239_p31
  have hstep := st239_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p33 : ((6840948708931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT239 (i+1))
      = (∑ i ∈ Finset.range 32, stT239 (i+1)) + stT239 33 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 32
    simpa using h
  have hprev := st239_p32
  have hstep := st239_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p34 : ((8550229668821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT239 (i+1))
      = (∑ i ∈ Finset.range 33, stT239 (i+1)) + stT239 34 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 33
    simpa using h
  have hprev := st239_p33
  have hstep := st239_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p35 : ((9814444828181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT239 (i+1))
      = (∑ i ∈ Finset.range 34, stT239 (i+1)) + stT239 35 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 34
    simpa using h
  have hprev := st239_p34
  have hstep := st239_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p36 : ((10456229571467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT239 (i+1))
      = (∑ i ∈ Finset.range 35, stT239 (i+1)) + stT239 36 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 35
    simpa using h
  have hprev := st239_p35
  have hstep := st239_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p37 : ((10669530568261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT239 (i+1))
      = (∑ i ∈ Finset.range 36, stT239 (i+1)) + stT239 37 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 36
    simpa using h
  have hprev := st239_p36
  have hstep := st239_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p38 : ((10733750776093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT239 (i+1))
      = (∑ i ∈ Finset.range 37, stT239 (i+1)) + stT239 38 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 37
    simpa using h
  have hprev := st239_p37
  have hstep := st239_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p39 : ((10916918107121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT239 (i+1))
      = (∑ i ∈ Finset.range 38, stT239 (i+1)) + stT239 39 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 38
    simpa using h
  have hprev := st239_p38
  have hstep := st239_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p40 : ((11454432294773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT239 (i+1))
      = (∑ i ∈ Finset.range 39, stT239 (i+1)) + stT239 40 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 39
    simpa using h
  have hprev := st239_p39
  have hstep := st239_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p41 : ((6247084817341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT239 (i+1))
      = (∑ i ∈ Finset.range 40, stT239 (i+1)) + stT239 41 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 40
    simpa using h
  have hprev := st239_p40
  have hstep := st239_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p42 : ((13959586531749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT239 (i+1))
      = (∑ i ∈ Finset.range 41, stT239 (i+1)) + stT239 42 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 41
    simpa using h
  have hprev := st239_p41
  have hstep := st239_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p43 : ((15396671396349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT239 (i+1))
      = (∑ i ∈ Finset.range 42, stT239 (i+1)) + stT239 43 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 42
    simpa using h
  have hprev := st239_p42
  have hstep := st239_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p44 : ((3208036144057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT239 (i+1))
      = (∑ i ∈ Finset.range 43, stT239 (i+1)) + stT239 44 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 43
    simpa using h
  have hprev := st239_p43
  have hstep := st239_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p45 : ((15363498840701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT239 (i+1))
      = (∑ i ∈ Finset.range 44, stT239 (i+1)) + stT239 45 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 44
    simpa using h
  have hprev := st239_p44
  have hstep := st239_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p46 : ((13892559946321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT239 (i+1))
      = (∑ i ∈ Finset.range 45, stT239 (i+1)) + stT239 46 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 45
    simpa using h
  have hprev := st239_p45
  have hstep := st239_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p47 : ((13196929761321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT239 (i+1))
      = (∑ i ∈ Finset.range 46, stT239 (i+1)) + stT239 47 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 46
    simpa using h
  have hprev := st239_p46
  have hstep := st239_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p48 : ((1773163527087/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT239 (i+1))
      = (∑ i ∈ Finset.range 47, stT239 (i+1)) + stT239 48 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 47
    simpa using h
  have hprev := st239_p47
  have hstep := st239_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p49 : ((7705723924427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT239 (i+1))
      = (∑ i ∈ Finset.range 48, stT239 (i+1)) + stT239 49 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 48
    simpa using h
  have hprev := st239_p48
  have hstep := st239_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p50 : ((7415631863463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT239 (i+1))
      = (∑ i ∈ Finset.range 49, stT239 (i+1)) + stT239 50 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 49
    simpa using h
  have hprev := st239_p49
  have hstep := st239_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p51 : ((13542676140891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT239 (i+1))
      = (∑ i ∈ Finset.range 50, stT239 (i+1)) + stT239 51 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 50
    simpa using h
  have hprev := st239_p50
  have hstep := st239_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p52 : ((14175225512391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT239 (i+1))
      = (∑ i ∈ Finset.range 51, stT239 (i+1)) + stT239 52 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 51
    simpa using h
  have hprev := st239_p51
  have hstep := st239_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p53 : ((15282167079321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT239 (i+1))
      = (∑ i ∈ Finset.range 52, stT239 (i+1)) + stT239 53 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 52
    simpa using h
  have hprev := st239_p52
  have hstep := st239_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p54 : ((14234511870273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT239 (i+1))
      = (∑ i ∈ Finset.range 53, stT239 (i+1)) + stT239 54 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 53
    simpa using h
  have hprev := st239_p53
  have hstep := st239_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p55 : ((13752769002273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT239 (i+1))
      = (∑ i ∈ Finset.range 54, stT239 (i+1)) + stT239 55 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 54
    simpa using h
  have hprev := st239_p54
  have hstep := st239_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p56 : ((15087903061911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT239 (i+1))
      = (∑ i ∈ Finset.range 55, stT239 (i+1)) + stT239 56 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 55
    simpa using h
  have hprev := st239_p55
  have hstep := st239_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p57 : ((2885283077463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT239 (i+1))
      = (∑ i ∈ Finset.range 56, stT239 (i+1)) + stT239 57 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 56
    simpa using h
  have hprev := st239_p56
  have hstep := st239_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p58 : ((86286605807/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT239 (i+1))
      = (∑ i ∈ Finset.range 57, stT239 (i+1)) + stT239 58 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 57
    simpa using h
  have hprev := st239_p57
  have hstep := st239_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p59 : ((15095897437331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT239 (i+1))
      = (∑ i ∈ Finset.range 58, stT239 (i+1)) + stT239 59 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 58
    simpa using h
  have hprev := st239_p58
  have hstep := st239_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p60 : ((14143050175691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT239 (i+1))
      = (∑ i ∈ Finset.range 59, stT239 (i+1)) + stT239 60 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 59
    simpa using h
  have hprev := st239_p59
  have hstep := st239_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p61 : ((14170158126987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT239 (i+1))
      = (∑ i ∈ Finset.range 60, stT239 (i+1)) + stT239 61 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 60
    simpa using h
  have hprev := st239_p60
  have hstep := st239_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p62 : ((7505397959453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT239 (i+1))
      = (∑ i ∈ Finset.range 61, stT239 (i+1)) + stT239 62 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 61
    simpa using h
  have hprev := st239_p61
  have hstep := st239_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p63 : ((344198278627/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT239 (i+1))
      = (∑ i ∈ Finset.range 62, stT239 (i+1)) + stT239 63 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 62
    simpa using h
  have hprev := st239_p62
  have hstep := st239_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p64 : ((372234341127/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT239 (i+1))
      = (∑ i ∈ Finset.range 63, stT239 (i+1)) + stT239 64 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 63
    simpa using h
  have hprev := st239_p63
  have hstep := st239_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p65 : ((222524099459/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT239 (i+1))
      = (∑ i ∈ Finset.range 64, stT239 (i+1)) + stT239 65 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 64
    simpa using h
  have hprev := st239_p64
  have hstep := st239_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p66 : ((3573335422081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT239 (i+1))
      = (∑ i ∈ Finset.range 65, stT239 (i+1)) + stT239 66 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 65
    simpa using h
  have hprev := st239_p65
  have hstep := st239_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p67 : ((7390309002653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT239 (i+1))
      = (∑ i ∈ Finset.range 66, stT239 (i+1)) + stT239 67 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 66
    simpa using h
  have hprev := st239_p66
  have hstep := st239_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p68 : ((3475654145271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT239 (i+1))
      = (∑ i ∈ Finset.range 67, stT239 (i+1)) + stT239 68 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 67
    simpa using h
  have hprev := st239_p67
  have hstep := st239_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p69 : ((1875604708197/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT239 (i+1))
      = (∑ i ∈ Finset.range 68, stT239 (i+1)) + stT239 69 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 68
    simpa using h
  have hprev := st239_p68
  have hstep := st239_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p70 : ((2763528359937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT239 (i+1))
      = (∑ i ∈ Finset.range 69, stT239 (i+1)) + stT239 70 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 69
    simpa using h
  have hprev := st239_p69
  have hstep := st239_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p71 : ((14994024224563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT239 (i+1))
      = (∑ i ∈ Finset.range 70, stT239 (i+1)) + stT239 71 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 70
    simpa using h
  have hprev := st239_p70
  have hstep := st239_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p72 : ((13880280887059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT239 (i+1))
      = (∑ i ∈ Finset.range 71, stT239 (i+1)) + stT239 72 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 71
    simpa using h
  have hprev := st239_p71
  have hstep := st239_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p73 : ((7456943028251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT239 (i+1))
      = (∑ i ∈ Finset.range 72, stT239 (i+1)) + stT239 73 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 72
    simpa using h
  have hprev := st239_p72
  have hstep := st239_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p74 : ((6976665655701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT239 (i+1))
      = (∑ i ∈ Finset.range 73, stT239 (i+1)) + stT239 74 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 73
    simpa using h
  have hprev := st239_p73
  have hstep := st239_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p75 : ((7430996227101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT239 (i+1))
      = (∑ i ∈ Finset.range 74, stT239 (i+1)) + stT239 75 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 74
    simpa using h
  have hprev := st239_p74
  have hstep := st239_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p76 : ((13976464672387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT239 (i+1))
      = (∑ i ∈ Finset.range 75, stT239 (i+1)) + stT239 76 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 75
    simpa using h
  have hprev := st239_p75
  have hstep := st239_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p77 : ((14868552024807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT239 (i+1))
      = (∑ i ∈ Finset.range 76, stT239 (i+1)) + stT239 77 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 76
    simpa using h
  have hprev := st239_p76
  have hstep := st239_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p78 : ((13942947595869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT239 (i+1))
      = (∑ i ∈ Finset.range 77, stT239 (i+1)) + stT239 78 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 77
    simpa using h
  have hprev := st239_p77
  have hstep := st239_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p79 : ((1492098910023/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT239 (i+1))
      = (∑ i ∈ Finset.range 78, stT239 (i+1)) + stT239 79 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 78
    simpa using h
  have hprev := st239_p78
  have hstep := st239_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p80 : ((1735417298841/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT239 (i+1))
      = (∑ i ∈ Finset.range 79, stT239 (i+1)) + stT239 80 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 79
    simpa using h
  have hprev := st239_p79
  have hstep := st239_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p81 : ((14970208282041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT239 (i+1))
      = (∑ i ∈ Finset.range 80, stT239 (i+1)) + stT239 81 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 80
    simpa using h
  have hprev := st239_p80
  have hstep := st239_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p82 : ((13865837066241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT239 (i+1))
      = (∑ i ∈ Finset.range 81, stT239 (i+1)) + stT239 82 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 81
    simpa using h
  have hprev := st239_p81
  have hstep := st239_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p83 : ((14930756162937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT239 (i+1))
      = (∑ i ∈ Finset.range 82, stT239 (i+1)) + stT239 83 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 82
    simpa using h
  have hprev := st239_p82
  have hstep := st239_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p84 : ((13985943143787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT239 (i+1))
      = (∑ i ∈ Finset.range 83, stT239 (i+1)) + stT239 84 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 83
    simpa using h
  have hprev := st239_p83
  have hstep := st239_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p85 : ((14712243477419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT239 (i+1))
      = (∑ i ∈ Finset.range 84, stT239 (i+1)) + stT239 85 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 84
    simpa using h
  have hprev := st239_p84
  have hstep := st239_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p86 : ((14304706663067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT239 (i+1))
      = (∑ i ∈ Finset.range 85, stT239 (i+1)) + stT239 86 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 85
    simpa using h
  have hprev := st239_p85
  have hstep := st239_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p87 : ((14314272046331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT239 (i+1))
      = (∑ i ∈ Finset.range 86, stT239 (i+1)) + stT239 87 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 86
    simpa using h
  have hprev := st239_p86
  have hstep := st239_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p88 : ((2946096025129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT239 (i+1))
      = (∑ i ∈ Finset.range 87, stT239 (i+1)) + stT239 88 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 87
    simpa using h
  have hprev := st239_p87
  have hstep := st239_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p89 : ((13939571097929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT239 (i+1))
      = (∑ i ∈ Finset.range 88, stT239 (i+1)) + stT239 89 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 88
    simpa using h
  have hprev := st239_p88
  have hstep := st239_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p90 : ((2991774136657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT239 (i+1))
      = (∑ i ∈ Finset.range 89, stT239 (i+1)) + stT239 90 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 89
    simpa using h
  have hprev := st239_p89
  have hstep := st239_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p91 : ((1394138953801/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT239 (i+1))
      = (∑ i ∈ Finset.range 90, stT239 (i+1)) + stT239 91 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 90
    simpa using h
  have hprev := st239_p90
  have hstep := st239_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p92 : ((7343895405983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT239 (i+1))
      = (∑ i ∈ Finset.range 91, stT239 (i+1)) + stT239 92 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 91
    simpa using h
  have hprev := st239_p91
  have hstep := st239_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p93 : ((7220511079883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT239 (i+1))
      = (∑ i ∈ Finset.range 92, stT239 (i+1)) + stT239 93 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 92
    simpa using h
  have hprev := st239_p92
  have hstep := st239_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p94 : ((7045983131841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT239 (i+1))
      = (∑ i ∈ Finset.range 93, stT239 (i+1)) + stT239 94 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 93
    simpa using h
  have hprev := st239_p93
  have hstep := st239_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p95 : ((1493100696817/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT239 (i+1))
      = (∑ i ∈ Finset.range 94, stT239 (i+1)) + stT239 95 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 94
    simpa using h
  have hprev := st239_p94
  have hstep := st239_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p96 : ((13910674803913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT239 (i+1))
      = (∑ i ∈ Finset.range 95, stT239 (i+1)) + stT239 96 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 95
    simpa using h
  have hprev := st239_p95
  have hstep := st239_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p97 : ((14693255779451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT239 (i+1))
      = (∑ i ∈ Finset.range 96, stT239 (i+1)) + stT239 97 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 96
    simpa using h
  have hprev := st239_p96
  have hstep := st239_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p98 : ((906413542177/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT239 (i+1))
      = (∑ i ∈ Finset.range 97, stT239 (i+1)) + stT239 98 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 97
    simpa using h
  have hprev := st239_p97
  have hstep := st239_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p99 : ((6999258375029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT239 (i+1))
      = (∑ i ∈ Finset.range 98, stT239 (i+1)) + stT239 99 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 98
    simpa using h
  have hprev := st239_p98
  have hstep := st239_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p100 : ((7476025898261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT239 (i+1))
      = (∑ i ∈ Finset.range 99, stT239 (i+1)) + stT239 100 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 99
    simpa using h
  have hprev := st239_p99
  have hstep := st239_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p101 : ((1405932957391/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT239 (i+1))
      = (∑ i ∈ Finset.range 100, stT239 (i+1)) + stT239 101 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 100
    simpa using h
  have hprev := st239_p100
  have hstep := st239_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p102 : ((14376684559321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT239 (i+1))
      = (∑ i ∈ Finset.range 101, stT239 (i+1)) + stT239 102 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 101
    simpa using h
  have hprev := st239_p101
  have hstep := st239_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p103 : ((7417374615743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT239 (i+1))
      = (∑ i ∈ Finset.range 102, stT239 (i+1)) + stT239 103 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 102
    simpa using h
  have hprev := st239_p102
  have hstep := st239_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p104 : ((13885787065831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT239 (i+1))
      = (∑ i ∈ Finset.range 103, stT239 (i+1)) + stT239 104 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 103
    simpa using h
  have hprev := st239_p103
  have hstep := st239_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p105 : ((14691378853231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT239 (i+1))
      = (∑ i ∈ Finset.range 104, stT239 (i+1)) + stT239 105 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 104
    simpa using h
  have hprev := st239_p104
  have hstep := st239_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p106 : ((14599228093981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT239 (i+1))
      = (∑ i ∈ Finset.range 105, stT239 (i+1)) + stT239 106 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 105
    simpa using h
  have hprev := st239_p105
  have hstep := st239_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p107 : ((13904028182541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT239 (i+1))
      = (∑ i ∈ Finset.range 106, stT239 (i+1)) + stT239 107 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 106
    simpa using h
  have hprev := st239_p106
  have hstep := st239_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p108 : ((14855426889291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT239 (i+1))
      = (∑ i ∈ Finset.range 107, stT239 (i+1)) + stT239 108 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 107
    simpa using h
  have hprev := st239_p107
  have hstep := st239_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p109 : ((3602847207047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT239 (i+1))
      = (∑ i ∈ Finset.range 108, stT239 (i+1)) + stT239 109 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 108
    simpa using h
  have hprev := st239_p108
  have hstep := st239_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p110 : ((13973641569869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT239 (i+1))
      = (∑ i ∈ Finset.range 109, stT239 (i+1)) + stT239 110 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 109
    simpa using h
  have hprev := st239_p109
  have hstep := st239_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p111 : ((745823052429/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT239 (i+1))
      = (∑ i ∈ Finset.range 110, stT239 (i+1)) + stT239 111 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 110
    simpa using h
  have hprev := st239_p110
  have hstep := st239_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p112 : ((3579120403721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT239 (i+1))
      = (∑ i ∈ Finset.range 111, stT239 (i+1)) + stT239 112 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 111
    simpa using h
  have hprev := st239_p111
  have hstep := st239_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p113 : ((14012283487277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT239 (i+1))
      = (∑ i ∈ Finset.range 112, stT239 (i+1)) + stT239 113 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 112
    simpa using h
  have hprev := st239_p112
  have hstep := st239_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p114 : ((1866134454559/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT239 (i+1))
      = (∑ i ∈ Finset.range 113, stT239 (i+1)) + stT239 114 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 113
    simpa using h
  have hprev := st239_p113
  have hstep := st239_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p115 : ((7156282437901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT239 (i+1))
      = (∑ i ∈ Finset.range 114, stT239 (i+1)) + stT239 115 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 114
    simpa using h
  have hprev := st239_p114
  have hstep := st239_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p116 : ((6997043061539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT239 (i+1))
      = (∑ i ∈ Finset.range 115, stT239 (i+1)) + stT239 116 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 115
    simpa using h
  have hprev := st239_p115
  have hstep := st239_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p117 : ((7455329730039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT239 (i+1))
      = (∑ i ∈ Finset.range 116, stT239 (i+1)) + stT239 117 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 116
    simpa using h
  have hprev := st239_p116
  have hstep := st239_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p118 : ((7197721545489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT239 (i+1))
      = (∑ i ∈ Finset.range 117, stT239 (i+1)) + stT239 118 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 117
    simpa using h
  have hprev := st239_p117
  have hstep := st239_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p119 : ((13931346804947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT239 (i+1))
      = (∑ i ∈ Finset.range 118, stT239 (i+1)) + stT239 119 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 118
    simpa using h
  have hprev := st239_p118
  have hstep := st239_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p120 : ((14839466229467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT239 (i+1))
      = (∑ i ∈ Finset.range 119, stT239 (i+1)) + stT239 120 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 119
    simpa using h
  have hprev := st239_p119
  have hstep := st239_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p121 : ((14561186201639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT239 (i+1))
      = (∑ i ∈ Finset.range 120, stT239 (i+1)) + stT239 121 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 120
    simpa using h
  have hprev := st239_p120
  have hstep := st239_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p122 : ((13872985560803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT239 (i+1))
      = (∑ i ∈ Finset.range 121, stT239 (i+1)) + stT239 122 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 121
    simpa using h
  have hprev := st239_p121
  have hstep := st239_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p123 : ((733568554093/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT239 (i+1))
      = (∑ i ∈ Finset.range 122, stT239 (i+1)) + stT239 123 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 122
    simpa using h
  have hprev := st239_p122
  have hstep := st239_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p124 : ((1847218680721/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT239 (i+1))
      = (∑ i ∈ Finset.range 123, stT239 (i+1)) + stT239 124 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 123
    simpa using h
  have hprev := st239_p123
  have hstep := st239_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p125 : ((695342647601/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT239 (i+1))
      = (∑ i ∈ Finset.range 124, stT239 (i+1)) + stT239 125 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 124
    simpa using h
  have hprev := st239_p124
  have hstep := st239_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p126 : ((1438282786649/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT239 (i+1))
      = (∑ i ∈ Finset.range 125, stT239 (i+1)) + stT239 126 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 125
    simpa using h
  have hprev := st239_p125
  have hstep := st239_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p127 : ((7473315398817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT239 (i+1))
      = (∑ i ∈ Finset.range 126, stT239 (i+1)) + stT239 127 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 126
    simpa using h
  have hprev := st239_p126
  have hstep := st239_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p128 : ((7063674055713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT239 (i+1))
      = (∑ i ∈ Finset.range 127, stT239 (i+1)) + stT239 128 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 127
    simpa using h
  have hprev := st239_p127
  have hstep := st239_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p129 : ((7021595541521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT239 (i+1))
      = (∑ i ∈ Finset.range 128, stT239 (i+1)) + stT239 129 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 128
    simpa using h
  have hprev := st239_p128
  have hstep := st239_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p130 : ((7453089659303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT239 (i+1))
      = (∑ i ∈ Finset.range 129, stT239 (i+1)) + stT239 130 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 129
    simpa using h
  have hprev := st239_p129
  have hstep := st239_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p131 : ((14534212520431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT239 (i+1))
      = (∑ i ∈ Finset.range 130, stT239 (i+1)) + stT239 131 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 130
    simpa using h
  have hprev := st239_p130
  have hstep := st239_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p132 : ((1386090657209/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT239 (i+1))
      = (∑ i ∈ Finset.range 131, stT239 (i+1)) + stT239 132 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 131
    simpa using h
  have hprev := st239_p131
  have hstep := st239_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p133 : ((7275212356009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT239 (i+1))
      = (∑ i ∈ Finset.range 132, stT239 (i+1)) + stT239 133 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 132
    simpa using h
  have hprev := st239_p132
  have hstep := st239_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p134 : ((7456005242653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT239 (i+1))
      = (∑ i ∈ Finset.range 133, stT239 (i+1)) + stT239 134 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 133
    simpa using h
  have hprev := st239_p133
  have hstep := st239_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p135 : ((14073145497107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT239 (i+1))
      = (∑ i ∈ Finset.range 134, stT239 (i+1)) + stT239 135 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 134
    simpa using h
  have hprev := st239_p134
  have hstep := st239_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p136 : ((7022526584467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT239 (i+1))
      = (∑ i ∈ Finset.range 135, stT239 (i+1)) + stT239 136 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 135
    simpa using h
  have hprev := st239_p135
  have hstep := st239_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p137 : ((2978020048141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT239 (i+1))
      = (∑ i ∈ Finset.range 136, stT239 (i+1)) + stT239 137 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 136
    simpa using h
  have hprev := st239_p136
  have hstep := st239_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p138 : ((2925296594589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT239 (i+1))
      = (∑ i ∈ Finset.range 137, stT239 (i+1)) + stT239 138 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 137
    simpa using h
  have hprev := st239_p137
  have hstep := st239_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p139 : ((1733761365481/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT239 (i+1))
      = (∑ i ∈ Finset.range 138, stT239 (i+1)) + stT239 139 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 138
    simpa using h
  have hprev := st239_p138
  have hstep := st239_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p140 : ((3588921919253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT239 (i+1))
      = (∑ i ∈ Finset.range 139, stT239 (i+1)) + stT239 140 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 139
    simpa using h
  have hprev := st239_p139
  have hstep := st239_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p141 : ((14976185375963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT239 (i+1))
      = (∑ i ∈ Finset.range 140, stT239 (i+1)) + stT239 141 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 140
    simpa using h
  have hprev := st239_p140
  have hstep := st239_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p142 : ((2867962704999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT239 (i+1))
      = (∑ i ∈ Finset.range 141, stT239 (i+1)) + stT239 142 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 141
    simpa using h
  have hprev := st239_p141
  have hstep := st239_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p143 : ((6932512845293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT239 (i+1))
      = (∑ i ∈ Finset.range 142, stT239 (i+1)) + stT239 143 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 142
    simpa using h
  have hprev := st239_p142
  have hstep := st239_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p144 : ((14592666232863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT239 (i+1))
      = (∑ i ∈ Finset.range 143, stT239 (i+1)) + stT239 144 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 143
    simpa using h
  have hprev := st239_p143
  have hstep := st239_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p145 : ((14935661174397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT239 (i+1))
      = (∑ i ∈ Finset.range 144, stT239 (i+1)) + stT239 145 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 144
    simpa using h
  have hprev := st239_p144
  have hstep := st239_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p146 : ((14159329504127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT239 (i+1))
      = (∑ i ∈ Finset.range 145, stT239 (i+1)) + stT239 146 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 145
    simpa using h
  have hprev := st239_p145
  have hstep := st239_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p147 : ((348018769793/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT239 (i+1))
      = (∑ i ∈ Finset.range 146, stT239 (i+1)) + stT239 147 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 146
    simpa using h
  have hprev := st239_p146
  have hstep := st239_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p148 : ((1471838499953/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT239 (i+1))
      = (∑ i ∈ Finset.range 147, stT239 (i+1)) + stT239 148 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 147
    simpa using h
  have hprev := st239_p147
  have hstep := st239_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p149 : ((744263527327/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT239 (i+1))
      = (∑ i ∈ Finset.range 148, stT239 (i+1)) + stT239 149 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 148
    simpa using h
  have hprev := st239_p148
  have hstep := st239_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p150 : ((2816307895427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT239 (i+1))
      = (∑ i ∈ Finset.range 149, stT239 (i+1)) + stT239 150 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 149
    simpa using h
  have hprev := st239_p149
  have hstep := st239_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p151 : ((2790356164217/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT239 (i+1))
      = (∑ i ∈ Finset.range 150, stT239 (i+1)) + stT239 151 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 150
    simpa using h
  have hprev := st239_p150
  have hstep := st239_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p152 : ((3688333447933/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT239 (i+1))
      = (∑ i ∈ Finset.range 151, stT239 (i+1)) + stT239 152 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 151
    simpa using h
  have hprev := st239_p151
  have hstep := st239_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p153 : ((1859951446097/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT239 (i+1))
      = (∑ i ∈ Finset.range 152, stT239 (i+1)) + stT239 153 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 152
    simpa using h
  have hprev := st239_p152
  have hstep := st239_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p154 : ((14085456079993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT239 (i+1))
      = (∑ i ∈ Finset.range 153, stT239 (i+1)) + stT239 154 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 153
    simpa using h
  have hprev := st239_p153
  have hstep := st239_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p155 : ((13930139838253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT239 (i+1))
      = (∑ i ∈ Finset.range 154, stT239 (i+1)) + stT239 155 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 154
    simpa using h
  have hprev := st239_p154
  have hstep := st239_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p156 : ((14709955992493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT239 (i+1))
      = (∑ i ∈ Finset.range 155, stT239 (i+1)) + stT239 156 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 155
    simpa using h
  have hprev := st239_p155
  have hstep := st239_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p157 : ((14924318699749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT239 (i+1))
      = (∑ i ∈ Finset.range 156, stT239 (i+1)) + stT239 157 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 156
    simpa using h
  have hprev := st239_p156
  have hstep := st239_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p158 : ((14170450325623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT239 (i+1))
      = (∑ i ∈ Finset.range 157, stT239 (i+1)) + stT239 158 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 157
    simpa using h
  have hprev := st239_p157
  have hstep := st239_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p159 : ((13870206389787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT239 (i+1))
      = (∑ i ∈ Finset.range 158, stT239 (i+1)) + stT239 159 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 158
    simpa using h
  have hprev := st239_p158
  have hstep := st239_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p160 : ((7289176518777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT239 (i+1))
      = (∑ i ∈ Finset.range 159, stT239 (i+1)) + stT239 160 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 159
    simpa using h
  have hprev := st239_p159
  have hstep := st239_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p161 : ((7492528601527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT239 (i+1))
      = (∑ i ∈ Finset.range 160, stT239 (i+1)) + stT239 161 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 160
    simpa using h
  have hprev := st239_p160
  have hstep := st239_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p162 : ((7175827723077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT239 (i+1))
      = (∑ i ∈ Finset.range 161, stT239 (i+1)) + stT239 162 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 161
    simpa using h
  have hprev := st239_p161
  have hstep := st239_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p163 : ((13827410242983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT239 (i+1))
      = (∑ i ∈ Finset.range 162, stT239 (i+1)) + stT239 163 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 162
    simpa using h
  have hprev := st239_p162
  have hstep := st239_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p164 : ((14347269209643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT239 (i+1))
      = (∑ i ∈ Finset.range 163, stT239 (i+1)) + stT239 164 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 163
    simpa using h
  have hprev := st239_p163
  have hstep := st239_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p165 : ((14985038126183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT239 (i+1))
      = (∑ i ∈ Finset.range 164, stT239 (i+1)) + stT239 165 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 164
    simpa using h
  have hprev := st239_p164
  have hstep := st239_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p166 : ((7311933950299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT239 (i+1))
      = (∑ i ∈ Finset.range 165, stT239 (i+1)) + stT239 166 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 165
    simpa using h
  have hprev := st239_p165
  have hstep := st239_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p167 : ((6948276909147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT239 (i+1))
      = (∑ i ∈ Finset.range 166, stT239 (i+1)) + stT239 167 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 166
    simpa using h
  have hprev := st239_p166
  have hstep := st239_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p168 : ((7026662548989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT239 (i+1))
      = (∑ i ∈ Finset.range 167, stT239 (i+1)) + stT239 168 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 167
    simpa using h
  have hprev := st239_p167
  have hstep := st239_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p169 : ((3705366274767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT239 (i+1))
      = (∑ i ∈ Finset.range 168, stT239 (i+1)) + stT239 169 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 168
    simpa using h
  have hprev := st239_p168
  have hstep := st239_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p170 : ((931528594159/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT239 (i+1))
      = (∑ i ∈ Finset.range 169, stT239 (i+1)) + stT239 170 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 169
    simpa using h
  have hprev := st239_p169
  have hstep := st239_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p171 : ((442779896657/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT239 (i+1))
      = (∑ i ∈ Finset.range 170, stT239 (i+1)) + stT239 171 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 170
    simpa using h
  have hprev := st239_p170
  have hstep := st239_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p172 : ((13834023255351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT239 (i+1))
      = (∑ i ∈ Finset.range 171, stT239 (i+1)) + stT239 172 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 171
    simpa using h
  have hprev := st239_p171
  have hstep := st239_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p173 : ((14443802236751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT239 (i+1))
      = (∑ i ∈ Finset.range 172, stT239 (i+1)) + stT239 173 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 172
    simpa using h
  have hprev := st239_p172
  have hstep := st239_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p174 : ((15004864501767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT239 (i+1))
      = (∑ i ∈ Finset.range 173, stT239 (i+1)) + stT239 174 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 173
    simpa using h
  have hprev := st239_p173
  have hstep := st239_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p175 : ((7309270847407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT239 (i+1))
      = (∑ i ∈ Finset.range 174, stT239 (i+1)) + stT239 175 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 174
    simpa using h
  have hprev := st239_p174
  have hstep := st239_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p176 : ((869047482257/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT239 (i+1))
      = (∑ i ∈ Finset.range 175, stT239 (i+1)) + stT239 176 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 175
    simpa using h
  have hprev := st239_p175
  have hstep := st239_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p177 : ((6993883871061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT239 (i+1))
      = (∑ i ∈ Finset.range 176, stT239 (i+1)) + stT239 177 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 176
    simpa using h
  have hprev := st239_p176
  have hstep := st239_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p178 : ((7366214894373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT239 (i+1))
      = (∑ i ∈ Finset.range 177, stT239 (i+1)) + stT239 178 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 177
    simpa using h
  have hprev := st239_p177
  have hstep := st239_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p179 : ((14985491099001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT239 (i+1))
      = (∑ i ∈ Finset.range 178, stT239 (i+1)) + stT239 179 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 178
    simpa using h
  have hprev := st239_p178
  have hstep := st239_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p180 : ((14363951401653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT239 (i+1))
      = (∑ i ∈ Finset.range 179, stT239 (i+1)) + stT239 180 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 179
    simpa using h
  have hprev := st239_p179
  have hstep := st239_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p181 : ((13814677208913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT239 (i+1))
      = (∑ i ∈ Finset.range 180, stT239 (i+1)) + stT239 181 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 180
    simpa using h
  have hprev := st239_p180
  have hstep := st239_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p182 : ((14160429839967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT239 (i+1))
      = (∑ i ∈ Finset.range 181, stT239 (i+1)) + stT239 182 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 181
    simpa using h
  have hprev := st239_p181
  have hstep := st239_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p183 : ((2976224896653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT239 (i+1))
      = (∑ i ∈ Finset.range 182, stT239 (i+1)) + stT239 183 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 182
    simpa using h
  have hprev := st239_p182
  have hstep := st239_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p184 : ((14913670786197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT239 (i+1))
      = (∑ i ∈ Finset.range 183, stT239 (i+1)) + stT239 184 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 183
    simpa using h
  have hprev := st239_p183
  have hstep := st239_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p185 : ((7107825524131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT239 (i+1))
      = (∑ i ∈ Finset.range 184, stT239 (i+1)) + stT239 185 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 184
    simpa using h
  have hprev := st239_p184
  have hstep := st239_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p186 : ((276007774111/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT239 (i+1))
      = (∑ i ∈ Finset.range 185, stT239 (i+1)) + stT239 186 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 185
    simpa using h
  have hprev := st239_p185
  have hstep := st239_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p187 : ((7129948314823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT239 (i+1))
      = (∑ i ∈ Finset.range 186, stT239 (i+1)) + stT239 187 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 186
    simpa using h
  have hprev := st239_p186
  have hstep := st239_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p188 : ((1493623961699/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT239 (i+1))
      = (∑ i ∈ Finset.range 187, stT239 (i+1)) + stT239 188 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 187
    simpa using h
  have hprev := st239_p187
  have hstep := st239_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p189 : ((3719427302963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT239 (i+1))
      = (∑ i ∈ Finset.range 188, stT239 (i+1)) + stT239 189 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 188
    simpa using h
  have hprev := st239_p188
  have hstep := st239_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p190 : ((14171150475581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT239 (i+1))
      = (∑ i ∈ Finset.range 189, stT239 (i+1)) + stT239 190 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 189
    simpa using h
  have hprev := st239_p189
  have hstep := st239_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p191 : ((13795826334481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT239 (i+1))
      = (∑ i ∈ Finset.range 190, stT239 (i+1)) + stT239 191 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 190
    simpa using h
  have hprev := st239_p190
  have hstep := st239_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p192 : ((7131115856829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT239 (i+1))
      = (∑ i ∈ Finset.range 191, stT239 (i+1)) + stT239 192 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 191
    simpa using h
  have hprev := st239_p191
  have hstep := st239_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p193 : ((14932380198473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT239 (i+1))
      = (∑ i ∈ Finset.range 192, stT239 (i+1)) + stT239 193 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 192
    simpa using h
  have hprev := st239_p192
  have hstep := st239_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p194 : ((1863145206853/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT239 (i+1))
      = (∑ i ∈ Finset.range 193, stT239 (i+1)) + stT239 194 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 193
    simpa using h
  have hprev := st239_p193
  have hstep := st239_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p195 : ((14221875514769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT239 (i+1))
      = (∑ i ∈ Finset.range 194, stT239 (i+1)) + stT239 195 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 194
    simpa using h
  have hprev := st239_p194
  have hstep := st239_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p196 : ((13788189627009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT239 (i+1))
      = (∑ i ∈ Finset.range 195, stT239 (i+1)) + stT239 196 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 195
    simpa using h
  have hprev := st239_p195
  have hstep := st239_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p197 : ((14168944994529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT239 (i+1))
      = (∑ i ∈ Finset.range 196, stT239 (i+1)) + stT239 197 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 196
    simpa using h
  have hprev := st239_p196
  have hstep := st239_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p198 : ((2972991147147/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT239 (i+1))
      = (∑ i ∈ Finset.range 197, stT239 (i+1)) + stT239 198 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 197
    simpa using h
  have hprev := st239_p197
  have hstep := st239_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p199 : ((14980344549391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT239 (i+1))
      = (∑ i ∈ Finset.range 198, stT239 (i+1)) + stT239 199 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 198
    simpa using h
  have hprev := st239_p198
  have hstep := st239_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p200 : ((1437249910873/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT239 (i+1))
      = (∑ i ∈ Finset.range 199, stT239 (i+1)) + stT239 200 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 199
    simpa using h
  have hprev := st239_p199
  have hstep := st239_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p201 : ((6906689899341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT239 (i+1))
      = (∑ i ∈ Finset.range 200, stT239 (i+1)) + stT239 201 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 200
    simpa using h
  have hprev := st239_p200
  have hstep := st239_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p202 : ((2800333737651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT239 (i+1))
      = (∑ i ∈ Finset.range 201, stT239 (i+1)) + stT239 202 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 201
    simpa using h
  have hprev := st239_p201
  have hstep := st239_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p203 : ((14698483598613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT239 (i+1))
      = (∑ i ∈ Finset.range 202, stT239 (i+1)) + stT239 203 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 202
    simpa using h
  have hprev := st239_p202
  have hstep := st239_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p204 : ((15043858459773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT239 (i+1))
      = (∑ i ∈ Finset.range 203, stT239 (i+1)) + stT239 204 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 203
    simpa using h
  have hprev := st239_p203
  have hstep := st239_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p205 : ((3654899661029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT239 (i+1))
      = (∑ i ∈ Finset.range 204, stT239 (i+1)) + stT239 205 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 204
    simpa using h
  have hprev := st239_p204
  have hstep := st239_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p206 : ((1742954633949/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT239 (i+1))
      = (∑ i ∈ Finset.range 205, stT239 (i+1)) + stT239 206 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 205
    simpa using h
  have hprev := st239_p205
  have hstep := st239_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p207 : ((13827101681007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT239 (i+1))
      = (∑ i ∈ Finset.range 206, stT239 (i+1)) + stT239 207 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 206
    simpa using h
  have hprev := st239_p206
  have hstep := st239_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p208 : ((14404224041757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT239 (i+1))
      = (∑ i ∈ Finset.range 207, stT239 (i+1)) + stT239 208 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 207
    simpa using h
  have hprev := st239_p207
  have hstep := st239_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p209 : ((14990652253817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT239 (i+1))
      = (∑ i ∈ Finset.range 208, stT239 (i+1)) + stT239 209 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 208
    simpa using h
  have hprev := st239_p208
  have hstep := st239_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p210 : ((14901900105293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT239 (i+1))
      = (∑ i ∈ Finset.range 209, stT239 (i+1)) + stT239 210 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 209
    simpa using h
  have hprev := st239_p209
  have hstep := st239_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p211 : ((7122758393407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT239 (i+1))
      = (∑ i ∈ Finset.range 210, stT239 (i+1)) + stT239 211 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 210
    simpa using h
  have hprev := st239_p210
  have hstep := st239_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p212 : ((2755741692673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT239 (i+1))
      = (∑ i ∈ Finset.range 211, stT239 (i+1)) + stT239 212 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 211
    simpa using h
  have hprev := st239_p211
  have hstep := st239_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p213 : ((14031199556177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT239 (i+1))
      = (∑ i ∈ Finset.range 212, stT239 (i+1)) + stT239 213 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 212
    simpa using h
  have hprev := st239_p212
  have hstep := st239_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p214 : ((7356442436731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT239 (i+1))
      = (∑ i ∈ Finset.range 213, stT239 (i+1)) + stT239 214 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 213
    simpa using h
  have hprev := st239_p213
  have hstep := st239_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p215 : ((1882237608013/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT239 (i+1))
      = (∑ i ∈ Finset.range 214, stT239 (i+1)) + stT239 215 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 214
    simpa using h
  have hprev := st239_p214
  have hstep := st239_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p216 : ((146857919733/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT239 (i+1))
      = (∑ i ∈ Finset.range 215, stT239 (i+1)) + stT239 216 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 215
    simpa using h
  have hprev := st239_p215
  have hstep := st239_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p217 : ((1401114359309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT239 (i+1))
      = (∑ i ∈ Finset.range 216, stT239 (i+1)) + stT239 217 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 216
    simpa using h
  have hprev := st239_p216
  have hstep := st239_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p218 : ((3443091095483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT239 (i+1))
      = (∑ i ∈ Finset.range 217, stT239 (i+1)) + stT239 218 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 217
    simpa using h
  have hprev := st239_p217
  have hstep := st239_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p219 : ((3556190548647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT239 (i+1))
      = (∑ i ∈ Finset.range 218, stT239 (i+1)) + stT239 219 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 218
    simpa using h
  have hprev := st239_p218
  have hstep := st239_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p220 : ((14877696283929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT239 (i+1))
      = (∑ i ∈ Finset.range 219, stT239 (i+1)) + stT239 220 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 219
    simpa using h
  have hprev := st239_p219
  have hstep := st239_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p221 : ((601378311393/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT239 (i+1))
      = (∑ i ∈ Finset.range 220, stT239 (i+1)) + stT239 221 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 220
    simpa using h
  have hprev := st239_p220
  have hstep := st239_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p222 : ((7266491684361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT239 (i+1))
      = (∑ i ∈ Finset.range 221, stT239 (i+1)) + stT239 222 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 221
    simpa using h
  have hprev := st239_p221
  have hstep := st239_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p223 : ((6951617566811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT239 (i+1))
      = (∑ i ∈ Finset.range 222, stT239 (i+1)) + stT239 223 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 222
    simpa using h
  have hprev := st239_p222
  have hstep := st239_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p224 : ((1725060884957/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT239 (i+1))
      = (∑ i ∈ Finset.range 223, stT239 (i+1)) + stT239 224 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 223
    simpa using h
  have hprev := st239_p223
  have hstep := st239_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p225 : ((716344794329/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT239 (i+1))
      = (∑ i ∈ Finset.range 224, stT239 (i+1)) + stT239 225 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 224
    simpa using h
  have hprev := st239_p224
  have hstep := st239_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p226 : ((1493971880383/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT239 (i+1))
      = (∑ i ∈ Finset.range 225, stT239 (i+1)) + stT239 226 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 225
    simpa using h
  have hprev := st239_p225
  have hstep := st239_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p227 : ((469271503289/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT239 (i+1))
      = (∑ i ∈ Finset.range 226, stT239 (i+1)) + stT239 227 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 226
    simpa using h
  have hprev := st239_p226
  have hstep := st239_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p228 : ((1810510298447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT239 (i+1))
      = (∑ i ∈ Finset.range 227, stT239 (i+1)) + stT239 228 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 227
    simpa using h
  have hprev := st239_p227
  have hstep := st239_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p229 : ((3469462420063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT239 (i+1))
      = (∑ i ∈ Finset.range 228, stT239 (i+1)) + stT239 229 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 228
    simpa using h
  have hprev := st239_p228
  have hstep := st239_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p230 : ((6899450996561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT239 (i+1))
      = (∑ i ∈ Finset.range 229, stT239 (i+1)) + stT239 230 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 229
    simpa using h
  have hprev := st239_p229
  have hstep := st239_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p231 : ((7160550955499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT239 (i+1))
      = (∑ i ∈ Finset.range 230, stT239 (i+1)) + stT239 231 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 230
    simpa using h
  have hprev := st239_p230
  have hstep := st239_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p232 : ((1493113240597/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT239 (i+1))
      = (∑ i ∈ Finset.range 231, stT239 (i+1)) + stT239 232 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 231
    simpa using h
  have hprev := st239_p231
  have hstep := st239_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p233 : ((15038275480157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT239 (i+1))
      = (∑ i ∈ Finset.range 232, stT239 (i+1)) + stT239 233 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 232
    simpa using h
  have hprev := st239_p232
  have hstep := st239_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p234 : ((14543153731967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT239 (i+1))
      = (∑ i ∈ Finset.range 233, stT239 (i+1)) + stT239 234 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 233
    simpa using h
  have hprev := st239_p233
  have hstep := st239_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p235 : ((6960707850211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT239 (i+1))
      = (∑ i ∈ Finset.range 234, stT239 (i+1)) + stT239 235 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 234
    simpa using h
  have hprev := st239_p234
  have hstep := st239_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p236 : ((6880702804041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT239 (i+1))
      = (∑ i ∈ Finset.range 235, stT239 (i+1)) + stT239 236 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 235
    simpa using h
  have hprev := st239_p235
  have hstep := st239_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p237 : ((2841987509913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT239 (i+1))
      = (∑ i ∈ Finset.range 236, stT239 (i+1)) + stT239 237 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 236
    simpa using h
  have hprev := st239_p236
  have hstep := st239_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p238 : ((28995063903/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT239 (i+1))
      = (∑ i ∈ Finset.range 237, stT239 (i+1)) + stT239 238 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 237
    simpa using h
  have hprev := st239_p237
  have hstep := st239_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p239 : ((7539952939943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT239 (i+1))
      = (∑ i ∈ Finset.range 238, stT239 (i+1)) + stT239 239 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 238
    simpa using h
  have hprev := st239_p238
  have hstep := st239_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p240 : ((367528723873/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT239 (i+1))
      = (∑ i ∈ Finset.range 239, stT239 (i+1)) + stT239 240 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 239
    simpa using h
  have hprev := st239_p239
  have hstep := st239_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p241 : ((7028881827503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT239 (i+1))
      = (∑ i ∈ Finset.range 240, stT239 (i+1)) + stT239 241 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 240
    simpa using h
  have hprev := st239_p240
  have hstep := st239_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p242 : ((3433026806089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT239 (i+1))
      = (∑ i ∈ Finset.range 241, stT239 (i+1)) + stT239 242 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 241
    simpa using h
  have hprev := st239_p241
  have hstep := st239_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p243 : ((3503408657839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT239 (i+1))
      = (∑ i ∈ Finset.range 242, stT239 (i+1)) + stT239 243 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 242
    simpa using h
  have hprev := st239_p242
  have hstep := st239_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p244 : ((146479711907/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT239 (i+1))
      = (∑ i ∈ Finset.range 243, stT239 (i+1)) + stT239 244 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 243
    simpa using h
  have hprev := st239_p243
  have hstep := st239_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p245 : ((471035065181/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT239 (i+1))
      = (∑ i ∈ Finset.range 244, stT239 (i+1)) + stT239 245 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 244
    simpa using h
  have hprev := st239_p244
  have hstep := st239_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p246 : ((2983645698367/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT239 (i+1))
      = (∑ i ∈ Finset.range 245, stT239 (i+1)) + stT239 246 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 245
    simpa using h
  have hprev := st239_p245
  have hstep := st239_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p247 : ((2864356004623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT239 (i+1))
      = (∑ i ∈ Finset.range 246, stT239 (i+1)) + stT239 247 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 246
    simpa using h
  have hprev := st239_p246
  have hstep := st239_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p248 : ((13801190963291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT239 (i+1))
      = (∑ i ∈ Finset.range 247, stT239 (i+1)) + stT239 248 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 247
    simpa using h
  have hprev := st239_p247
  have hstep := st239_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p249 : ((13801630134023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT239 (i+1))
      = (∑ i ∈ Finset.range 248, stT239 (i+1)) + stT239 249 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 248
    simpa using h
  have hprev := st239_p248
  have hstep := st239_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_p250 : ((894951284643/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT239 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT239 (i+1))
      = (∑ i ∈ Finset.range 249, stT239 (i+1)) + stT239 250 := by
    have h := Finset.sum_range_succ (fun i => stT239 (i+1)) 249
    simpa using h
  have hprev := st239_p249
  have hstep := st239_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st239_s250 :
    |Real.sin (((239 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((77237/100000 : ℚ) : ℝ))
      - ((-287301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -765147/5000000) (δ := 6047/500000000) (ψ := 77237/100000) 239 210
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 239`** (evaluated boundary). -/
theorem station_239_sign : 0 < hardyG ((((239:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 239 250 (by norm_num) (by norm_num)
    ((77237/100000 : ℚ) : ℝ)
  have hchain := st239_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT239 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((239 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((77237/100000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st239_c250
  have hsinb := abs_le.mp st239_s250
  have hbdy_lo : ((34635433328143/913940000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((239 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((77237/100000 : ℚ) : ℝ))) / 2
          - ((((239:ℕ)):ℝ))
            * Real.sin (((239 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((77237/100000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((239:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((239:ℝ) * Real.log (250:ℝ) - ((77237/100000 : ℚ) : ℝ))) / 2
        - ((239:ℝ)) * Real.sin ((239:ℝ) * Real.log (250:ℝ) - ((77237/100000 : ℚ) : ℝ))
        ≥ ((273817373/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((239:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((273817373/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((273817373/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((273817373/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((239:ℕ)):ℝ))+1) * (((((239:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2457644959/1953125000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((894951284643/625000000000 : ℚ) : ℝ) + ((34635433328143/913940000000000 : ℚ) : ℝ)
      - ((2457644959/1953125000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((77237/100000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((239:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((77237/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((239:ℕ)):ℝ)))).re
      - Real.sin ((77237/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((239:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((239:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((239:ℕ)):ℝ))
      = (((((239:ℕ)):ℝ)) * (Real.log ((((239:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((239:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_239
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
  have hθwin : |(((77237/100000 : ℚ) : ℝ) + ((50:ℤ)) * (2*Real.pi)) - theta ((((239:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((239:ℕ)):ℝ)))
    (φ := ((77237/100000 : ℚ) : ℝ) + ((50:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((77237/100000 : ℚ)) : ℝ) 50).1,
    (cos_sin_shift (((77237/100000 : ℚ)) : ℝ) 50).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_239_sign
end AxiomAudit
