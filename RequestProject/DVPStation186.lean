import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 186` (rung-199.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT186 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((186 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-272131/200000 : ℚ) : ℝ))

theorem st186_c1 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((104299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1700819/5000000) (δ := 201/1000000000) (ψ := -272131/200000) 186 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t1 : ((52137/250000 : ℚ) : ℝ) ≤ stT186 1 := by
  have hc : ((52137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52137/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((52137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c2 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-22487/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2076083/5000000) (δ := 2363/250000000) (ψ := -272131/200000) 186 21
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t2 : ((-79547747233/1250000000000 : ℚ) : ℝ) ≤ stT186 2 := by
  have hc : ((-44999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79547747233/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-44999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c3 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-17931/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2053227/5000000) (δ := 4669/500000000) (ψ := -272131/200000) 186 33
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t3 : ((-207193702161/5000000000000 : ℚ) : ℝ) ≤ stT186 3 := by
  have hc : ((-35887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207193702161/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-35887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c4 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-15003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 125063/312500) (δ := 9407/1000000000) (ψ := -272131/200000) 186 41
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t4 : ((-18785003757/1250000000000 : ℚ) : ℝ) ≤ stT186 4 := by
  have hc : ((-3757/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18785003757/1250000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-3757/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c5 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((639629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2191953/10000000) (δ := 9457/1000000000) (ψ := -272131/200000) 186 48
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t5 : ((572056726233/2000000000000 : ℚ) : ℝ) ≤ stT186 5 := by
  have hc : ((639579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572056726233/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((639579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c6 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-48277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4047729/10000000) (δ := 4741/500000000) (ψ := -272131/200000) 186 53
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t6 : ((-197294155941/10000000000000 : ℚ) : ℝ) ≤ stT186 6 := by
  have hc : ((-48327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197294155941/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-48327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c7 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((431353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703003/2500000) (δ := 4709/500000000) (ψ := -272131/200000) 186 58
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t7 : ((407542949033/2500000000000 : ℚ) : ℝ) ≤ stT186 7 := by
  have hc : ((431303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407542949033/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((431303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c8 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((18691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -887941/2500000) (δ := 9447/1000000000) (ψ := -272131/200000) 186 62
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t8 : ((264242200887/5000000000000 : ℚ) : ℝ) ≤ stT186 8 := by
  have hc : ((74739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264242200887/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((74739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c9 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-66531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4093441/10000000) (δ := 1171/125000000) (ψ := -272131/200000) 186 65
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t9 : ((-110968355527/5000000000000 : ℚ) : ℝ) ≤ stT186 9 := by
  have hc : ((-66581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110968355527/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-66581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c10 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-181773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 745273/1250000) (δ := 949/100000000) (ψ := -272131/200000) 186 68
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t10 : ((-574856287369/2500000000000 : ℚ) : ℝ) ≤ stT186 10 := by
  have hc : ((-363571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-574856287369/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-363571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c11 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((60589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3157537/10000000) (δ := 9411/1000000000) (ψ := -272131/200000) 186 71
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t11 : ((182652530427/2000000000000 : ℚ) : ℝ) ≤ stT186 11 := by
  have hc : ((60579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182652530427/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((60579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c12 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((167581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -876513/2500000) (δ := 9333/1000000000) (ψ := -272131/200000) 186 74
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t12 : ((483620281781/10000000000000 : ℚ) : ℝ) ≤ stT186 12 := by
  have hc : ((167531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((483620281781/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((167531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c13 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((18953/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2297877/10000000) (δ := 9347/1000000000) (ψ := -272131/200000) 186 76
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t13 : ((1681977981/10000000000 : ℚ) : ℝ) ≤ stT186 13 := by
  have hc : ((303223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1681977981/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((303223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c14 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-536321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 534217/1000000) (δ := 9441/1000000000) (ψ := -272131/200000) 186 78
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t14 : ((-1433512107423/10000000000000 : ℚ) : ℝ) ≤ stT186 14 := by
  have hc : ((-536371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1433512107423/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-536371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c15 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-46221/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3003971/5000000) (δ := 9427/1000000000) (ψ := -272131/200000) 186 80
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t15 : ((-954801458277/5000000000000 : ℚ) : ℝ) ≤ stT186 15 := by
  have hc : ((-369793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-954801458277/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-369793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c16 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-16681/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2301209/5000000) (δ := 9413/1000000000) (ψ := -272131/200000) 186 82
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t16 : ((-333682633473/5000000000000 : ℚ) : ℝ) ≤ stT186 16 := by
  have hc : ((-133473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333682633473/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-133473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c17 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((852121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1376931/10000000) (δ := 1881/200000000) (ψ := -272131/200000) 186 84
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t17 : ((516643878069/2500000000000 : ℚ) : ℝ) ≤ stT186 17 := by
  have hc : ((852071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516643878069/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((852071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c18 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((92789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173017/500000) (δ := 1173/125000000) (ψ := -272131/200000) 186 86
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t18 : ((27330848601/625000000000 : ℚ) : ℝ) ≤ stT186 18 := by
  have hc : ((23191/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27330848601/625000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((23191/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c19 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-730041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1194589/2000000) (δ := 4663/500000000) (ψ := -272131/200000) 186 87
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t19 : ((-837472054189/5000000000000 : ℚ) : ℝ) ≤ stT186 19 := by
  have hc : ((-730091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837472054189/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-730091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c20 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((804099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1591597/10000000) (δ := 467/50000000) (ψ := -272131/200000) 186 89
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t20 : ((1797907435283/10000000000000 : ℚ) : ℝ) ≤ stT186 20 := by
  have hc : ((804049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1797907435283/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((804049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c21 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-551663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5387883/10000000) (δ := 1181/125000000) (ψ := -272131/200000) 186 90
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t21 : ((-1203936522627/10000000000000 : ℚ) : ℝ) ≤ stT186 21 := by
  have hc : ((-551713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1203936522627/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-551713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c22 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-186601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1099061/2500000) (δ := 9341/1000000000) (ψ := -272131/200000) 186 92
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t22 : ((-49742678151/1250000000000 : ℚ) : ℝ) ≤ stT186 22 := by
  have hc : ((-186651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49742678151/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-186651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c23 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((243623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14147/250000) (δ := 9369/1000000000) (ψ := -272131/200000) 186 93
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t23 : ((126990743103/625000000000 : ℚ) : ℝ) ≤ stT186 23 := by
  have hc : ((487221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126990743103/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((487221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c24 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-35559/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4648131/10000000) (δ := 2369/250000000) (ψ := -272131/200000) 186 94
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t24 : ((-145194564081/2500000000000 : ℚ) : ℝ) ≤ stT186 24 := by
  have hc : ((-142261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145194564081/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-142261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c25 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-499813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3892783/5000000) (δ := 291/31250000) (ψ := -272131/200000) 186 96
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t25 : ((-499838249919/2500000000000 : ℚ) : ℝ) ≤ stT186 25 := by
  have hc : ((-249919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499838249919/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-249919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c26 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-506883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164247/312500) (δ := 1881/200000000) (ψ := -272131/200000) 186 97
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t26 : ((-497088868073/5000000000000 : ℚ) : ℝ) ≤ stT186 26 := by
  have hc : ((-506933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497088868073/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-506933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c27 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((203513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -853657/2500000) (δ := 4749/500000000) (ψ := -272131/200000) 186 98
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t27 : ((783129087/20000000000 : ℚ) : ℝ) ≤ stT186 27 := by
  have hc : ((203463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((783129087/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((203463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c28 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((126713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221161/1000000) (δ := 2353/250000000) (ψ := -272131/200000) 186 99
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t28 : ((119723058433/1000000000000 : ℚ) : ℝ) ≤ stT186 28 := by
  have hc : ((126703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119723058433/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((126703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c29 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((801589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1602119/10000000) (δ := 9319/1000000000) (ψ := -272131/200000) 186 100
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t29 : ((1488420250667/10000000000000 : ℚ) : ℝ) ≤ stT186 29 := by
  have hc : ((801539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1488420250667/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((801539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c30 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((407417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -309177/2000000) (δ := 293/31250000) (ψ := -272131/200000) 186 101
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t30 : ((23243508671/156250000000 : ℚ) : ℝ) ≤ stT186 30 := by
  have hc : ((12731/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23243508671/156250000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((12731/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c31 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((347413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401309/2000000) (δ := 9469/1000000000) (ψ := -272131/200000) 186 102
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t31 : ((155981814891/1250000000000 : ℚ) : ℝ) ≤ stT186 31 := by
  have hc : ((86847/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155981814891/1250000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((86847/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c32 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((380421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1475681/5000000) (δ := 9441/1000000000) (ψ := -272131/200000) 186 103
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t32 : ((336203460593/5000000000000 : ℚ) : ℝ) ≤ stT186 32 := by
  have hc : ((380371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336203460593/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((380371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c33 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-168607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1087633/2500000) (δ := 1891/200000000) (ψ := -272131/200000) 186 104
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t33 : ((-293594226489/10000000000000 : ℚ) : ℝ) ≤ stT186 33 := by
  have hc : ((-168657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293594226489/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-168657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c34 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-195823/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123537/200000) (δ := 2337/250000000) (ψ := -272131/200000) 186 105
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t34 : ((-335855140803/2500000000000 : ℚ) : ℝ) ≤ stT186 34 := by
  have hc : ((-391671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335855140803/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-391671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c35 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-487877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3651169/5000000) (δ := 1891/200000000) (ψ := -272131/200000) 186 105
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t35 : ((-412352570859/2500000000000 : ℚ) : ℝ) ≤ stT186 35 := by
  have hc : ((-243951/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-412352570859/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-243951/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c36 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-301953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4693843/10000000) (δ := 9363/1000000000) (ψ := -272131/200000) 186 106
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t36 : ((-503338434001/10000000000000 : ℚ) : ℝ) ≤ stT186 36 := by
  have hc : ((-302003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503338434001/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-302003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c37 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((385443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 345283/2000000) (δ := 947/100000000) (ψ := -272131/200000) 186 107
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t37 : ((316811476201/2500000000000 : ℚ) : ℝ) ≤ stT186 37 := by
  have hc : ((192709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316811476201/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((192709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c38 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((16133/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -395209/2500000) (δ := 4713/500000000) (ψ := -272131/200000) 186 108
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t38 : ((3271194531/25000000000 : ℚ) : ℝ) ≤ stT186 38 := by
  have hc : ((4033/5000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3271194531/25000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((4033/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c39 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-491037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5210191/10000000) (δ := 2371/250000000) (ψ := -272131/200000) 186 109
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t39 : ((-393184386767/5000000000000 : ℚ) : ℝ) ≤ stT186 39 := by
  have hc : ((-491087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393184386767/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-491087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c40 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-217381/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3281293/5000000) (δ := 2371/250000000) (ψ := -272131/200000) 186 109
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t40 : ((-687458682393/5000000000000 : ℚ) : ℝ) ≤ stT186 40 := by
  have hc : ((-434787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-687458682393/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-434787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c41 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((297041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2336681/10000000) (δ := 2353/250000000) (ψ := -272131/200000) 186 110
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t41 : ((57982609599/625000000000 : ℚ) : ℝ) ≤ stT186 41 := by
  have hc : ((37127/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57982609599/625000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((37127/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c42 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((129521/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1082949/5000000) (δ := 1861/200000000) (ψ := -272131/200000) 186 111
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t42 : ((199839746863/2000000000000 : ℚ) : ℝ) ≤ stT186 42 := by
  have hc : ((129511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199839746863/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((129511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c43 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-932789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6932179/10000000) (δ := 9397/1000000000) (ψ := -272131/200000) 186 112
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t43 : ((-711283207627/5000000000000 : ℚ) : ℝ) ≤ stT186 43 := by
  have hc : ((-932839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-711283207627/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-932839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c44 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((67569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3757939/10000000) (δ := 4703/500000000) (ψ := -272131/200000) 186 112
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t44 : ((25447168391/2500000000000 : ℚ) : ℝ) ≤ stT186 44 := by
  have hc : ((67519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25447168391/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((67519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c45 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((825297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1500173/10000000) (δ := 949/100000000) (ψ := -272131/200000) 186 113
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t45 : ((1230204780617/10000000000000 : ℚ) : ℝ) ≤ stT186 45 := by
  have hc : ((825247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1230204780617/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((825247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c46 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-235149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6987947/10000000) (δ := 471/50000000) (ψ := -272131/200000) 186 114
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t46 : ((-34672681883/250000000000 : ℚ) : ℝ) ≤ stT186 46 := by
  have hc : ((-470323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34672681883/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-470323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c47 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((3577/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506241/5000000) (δ := 9383/1000000000) (ψ := -272131/200000) 186 114
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t47 : ((10433716297/200000000000 : ℚ) : ℝ) ≤ stT186 47 := by
  have hc : ((7153/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10433716297/200000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((7153/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c48 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((397267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58113/200000) (δ := 9327/1000000000) (ψ := -272131/200000) 186 115
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t48 : ((4586664699/80000000000 : ℚ) : ℝ) ≤ stT186 48 := by
  have hc : ((397217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4586664699/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((397217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c49 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-178433/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3341139/5000000) (δ := 9327/1000000000) (ψ := -272131/200000) 186 115
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t49 : ((-63729668349/500000000000 : ℚ) : ℝ) ≤ stT186 49 := by
  have hc : ((-178443/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63729668349/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-178443/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c50 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((989149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 368617/10000000) (δ := 4717/500000000) (ψ := -272131/200000) 186 116
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t50 : ((1398796664087/10000000000000 : ℚ) : ℝ) ≤ stT186 50 := by
  have hc : ((989099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1398796664087/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((989099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c51 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-154359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3065569/5000000) (δ := 9461/1000000000) (ψ := -272131/200000) 186 117
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t51 : ((-216159977689/2000000000000 : ℚ) : ℝ) ≤ stT186 51 := by
  have hc : ((-154369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216159977689/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-154369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c52 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((399971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2898279/10000000) (δ := 4671/500000000) (ψ := -272131/200000) 186 117
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t52 : ((2218361787/40000000000 : ℚ) : ℝ) ≤ stT186 52 := by
  have hc : ((399921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2218361787/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((399921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c53 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-158/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3952271/10000000) (δ := 9449/1000000000) (ψ := -272131/200000) 186 118
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t53 : ((-3489646043/2500000000000 : ℚ) : ℝ) ≤ stT186 53 := by
  have hc : ((-5081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3489646043/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-5081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c54 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-319333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947911/2000000) (δ := 4677/500000000) (ψ := -272131/200000) 186 118
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t54 : ((-108656332281/2500000000000 : ℚ) : ℝ) ≤ stT186 54 := by
  have hc : ((-319383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108656332281/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-319383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c55 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((561639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2436077/10000000) (δ := 9447/1000000000) (ψ := -272131/200000) 186 119
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t55 : ((757246046011/10000000000000 : ℚ) : ℝ) ≤ stT186 55 := by
  have hc : ((561589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((757246046011/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((561589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c56 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-90209/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2971263/5000000) (δ := 2339/250000000) (ψ := -272131/200000) 186 119
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t56 : ((-482221080327/5000000000000 : ℚ) : ℝ) ≤ stT186 56 := by
  have hc : ((-360861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482221080327/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-360861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c57 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((408661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1535123/10000000) (δ := 9463/1000000000) (ψ := -272131/200000) 186 120
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t57 : ((33828216147/312500000000 : ℚ) : ℝ) ≤ stT186 57 := by
  have hc : ((102159/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33828216147/312500000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((102159/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c58 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-433719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51188/78125) (δ := 9463/1000000000) (ψ := -272131/200000) 186 120
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t58 : ((-7119175817/62500000000 : ℚ) : ℝ) ≤ stT186 58 := by
  have hc : ((-27109/31250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7119175817/62500000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-27109/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c59 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((442849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301751/2500000) (δ := 9433/1000000000) (ψ := -272131/200000) 186 121
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t59 : ((72063461817/625000000000 : ℚ) : ℝ) ≤ stT186 59 := by
  have hc : ((55353/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72063461817/625000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((55353/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c60 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-878409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3304149/5000000) (δ := 937/100000000) (ψ := -272131/200000) 186 121
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t60 : ((-226817235341/2000000000000 : ℚ) : ℝ) ≤ stT186 60 := by
  have hc : ((-878459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226817235341/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-878459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c61 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((422183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1413541/10000000) (δ := 4663/500000000) (ψ := -272131/200000) 186 122
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t61 : ((16891174817/156250000000 : ℚ) : ℝ) ≤ stT186 61 := by
  have hc : ((211079/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16891174817/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((211079/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c62 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-775963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 768449/1250000) (δ := 9477/1000000000) (ψ := -272131/200000) 186 122
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t62 : ((-492769031013/5000000000000 : ℚ) : ℝ) ≤ stT186 62 := by
  have hc : ((-776013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492769031013/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-776013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c63 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((661429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060093/5000000) (δ := 4709/500000000) (ψ := -272131/200000) 186 123
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t63 : ((833258835899/10000000000000 : ℚ) : ℝ) ≤ stT186 63 := by
  have hc : ((661379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((833258835899/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((661379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c64 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-488451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2601387/5000000) (δ := 1877/200000000) (ψ := -272131/200000) 186 123
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t64 : ((-610626738501/10000000000000 : ℚ) : ℝ) ≤ stT186 64 := by
  have hc : ((-488501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-610626738501/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-488501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c65 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((249827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -411967/1250000) (δ := 2373/250000000) (ψ := -272131/200000) 186 124
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t65 : ((309810152619/10000000000000 : ℚ) : ℝ) ≤ stT186 65 := by
  have hc : ((249777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309810152619/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((249777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c66 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((12329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3803651/10000000) (δ := 9311/1000000000) (ψ := -272131/200000) 186 124
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t66 : ((15160552281/2500000000000 : ℚ) : ℝ) ≤ stT186 66 := by
  have hc : ((24633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15160552281/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((24633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c67 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-191887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4911689/10000000) (δ := 2351/250000000) (ψ := -272131/200000) 186 125
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t67 : ((-5861448271/125000000000 : ℚ) : ℝ) ≤ stT186 67 := by
  have hc : ((-23989/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5861448271/125000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-23989/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c68 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((351591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1977333/10000000) (δ := 9399/1000000000) (ψ := -272131/200000) 186 125
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t68 : ((106584088437/1250000000000 : ℚ) : ℝ) ≤ stT186 68 := by
  have hc : ((175783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106584088437/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((175783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c69 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-37369/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6942189/10000000) (δ := 9497/1000000000) (ψ := -272131/200000) 186 126
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t69 : ((-44989414689/400000000000 : ℚ) : ℝ) ≤ stT186 69 := by
  have hc : ((-37371/40000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44989414689/400000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-37371/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c70 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((497473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251443/10000000) (δ := 4653/500000000) (ψ := -272131/200000) 186 126
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t70 : ((18580118067/156250000000 : ℚ) : ℝ) ≤ stT186 70 := by
  have hc : ((62181/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18580118067/156250000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((62181/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c71 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-164633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1586099/2500000) (δ := 4653/500000000) (ψ := -272131/200000) 186 126
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t71 : ((-97697674413/1000000000000 : ℚ) : ℝ) ≤ stT186 71 := by
  have hc : ((-164643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97697674413/1000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-164643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c72 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((413979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1429969/5000000) (δ := 939/100000000) (ψ := -272131/200000) 186 127
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t72 : ((487819879719/10000000000000 : ℚ) : ℝ) ≤ stT186 72 := by
  have hc : ((413929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487819879719/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((413929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c73 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((18583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3553947/10000000) (δ := 9413/1000000000) (ψ := -272131/200000) 186 127
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t73 : ((86969730177/5000000000000 : ℚ) : ℝ) ≤ stT186 73 := by
  have hc : ((74307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86969730177/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((74307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c74 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-172261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5827413/10000000) (δ := 9483/1000000000) (ψ := -272131/200000) 186 128
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t74 : ((-400527962919/5000000000000 : ℚ) : ℝ) ≤ stT186 74 := by
  have hc : ((-344547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400527962919/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-344547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c75 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((493149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414329/10000000) (δ := 233/25000000) (ψ := -272131/200000) 186 128
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t75 : ((1423525707/12500000000 : ℚ) : ℝ) ≤ stT186 75 := by
  have hc : ((123281/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1423525707/12500000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((123281/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c76 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-435821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6573347/10000000) (δ := 233/25000000) (ψ := -272131/200000) 186 128
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t76 : ((-249974896917/2500000000000 : ℚ) : ℝ) ≤ stT186 76 := by
  have hc : ((-217923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249974896917/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-217923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c77 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((341357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305609/1000000) (δ := 3/320000) (ψ := -272131/200000) 186 129
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t77 : ((77791032747/2000000000000 : ℚ) : ℝ) ≤ stT186 77 := by
  have hc : ((341307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77791032747/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((341307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c78 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((191573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2943991/10000000) (δ := 3/320000) (ψ := -272131/200000) 186 129
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t78 : ((54221348699/1250000000000 : ℚ) : ℝ) ≤ stT186 78 := by
  have hc : ((47887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54221348699/1250000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((47887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c79 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-459461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6840337/10000000) (δ := 1867/200000000) (ψ := -272131/200000) 186 130
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t79 : ((-8077534137/78125000000 : ℚ) : ℝ) ≤ stT186 79 := by
  have hc : ((-229743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8077534137/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-229743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c80 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((922427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -198239/2000000) (δ := 1867/200000000) (ψ := -272131/200000) 186 130
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t80 : ((1031247924441/10000000000000 : ℚ) : ℝ) ≤ stT186 80 := by
  have hc : ((922377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1031247924441/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((922377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c81 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-168303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4785267/10000000) (δ := 2367/250000000) (ψ := -272131/200000) 186 130
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t81 : ((-2922363449/78125000000 : ℚ) : ℝ) ≤ stT186 81 := by
  have hc : ((-21041/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2922363449/78125000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-21041/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c82 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-493443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5217099/10000000) (δ := 4721/500000000) (ψ := -272131/200000) 186 131
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t82 : ((-136243053947/2500000000000 : ℚ) : ℝ) ≤ stT186 82 := by
  have hc : ((-493493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136243053947/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-493493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c83 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((246491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52419/1250000) (δ := 4721/500000000) (ψ := -272131/200000) 186 131
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t83 : ((270545153697/2500000000000 : ℚ) : ℝ) ≤ stT186 83 := by
  have hc : ((492957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270545153697/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((492957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c84 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-367107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5988261/10000000) (δ := 18761/1000000000) (ψ := -272131/200000) 186 131
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t84 : ((-10014351347/125000000000 : ℚ) : ℝ) ≤ stT186 84 := by
  have hc : ((-91783/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10014351347/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-91783/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c85 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-57809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4216683/10000000) (δ := 4727/500000000) (ψ := -272131/200000) 186 132
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t85 : ((-31364910801/2500000000000 : ℚ) : ℝ) ≤ stT186 85 := by
  have hc : ((-28917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31364910801/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-28917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c86 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((176581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1221957/10000000) (δ := 4727/500000000) (ψ := -272131/200000) 186 132
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t86 : ((190401276717/2000000000000 : ℚ) : ℝ) ≤ stT186 86 := by
  have hc : ((176571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190401276717/2000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((176571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c87 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-87639/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412361/625000) (δ := 9349/1000000000) (ψ := -272131/200000) 186 132
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t87 : ((-23491067943/250000000000 : ℚ) : ℝ) ≤ stT186 87 := by
  have hc : ((-21911/25000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23491067943/250000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-21911/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c88 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((10487/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1897921/5000000) (δ := 9347/1000000000) (ψ := -272131/200000) 186 133
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t88 : ((11168513431/2000000000000 : ℚ) : ℝ) ≤ stT186 88 := by
  have hc : ((10477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11168513431/2000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((10477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c89 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((834611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729213/5000000) (δ := 591/62500000) (ψ := -272131/200000) 186 133
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t89 : ((884632156317/10000000000000 : ℚ) : ℝ) ≤ stT186 89 := by
  have hc : ((834561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((884632156317/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((834561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c90 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-887/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665401/1000000) (δ := 9347/1000000000) (ψ := -272131/200000) 186 133
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t90 : ((-18700663913/200000000000 : ℚ) : ℝ) ≤ stT186 90 := by
  have hc : ((-17741/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18700663913/200000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-17741/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c91 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((4487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3915773/10000000) (δ := 18639/1000000000) (ψ := -272131/200000) 186 134
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t91 : ((1162809027/2500000000000 : ℚ) : ℝ) ≤ stT186 91 := by
  have hc : ((4437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1162809027/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((4437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c92 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((893151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233247/2000000) (δ := 9439/1000000000) (ψ := -272131/200000) 186 134
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t92 : ((232780523943/2500000000000 : ℚ) : ℝ) ≤ stT186 92 := by
  have hc : ((893101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232780523943/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((893101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c93 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-393683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774163/1250000) (δ := 2341/250000000) (ψ := -272131/200000) 186 134
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t93 : ((-12758009313/156250000000 : ℚ) : ℝ) ≤ stT186 93 := by
  have hc : ((-98427/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12758009313/156250000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-98427/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c94 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-60819/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908269/2000000) (δ := 2333/250000000) (ψ := -272131/200000) 186 135
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t94 : ((-62742947393/2500000000000 : ℚ) : ℝ) ≤ stT186 94 := by
  have hc : ((-121663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62742947393/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-121663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c95 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((988511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94833/2500000) (δ := 9471/1000000000) (ψ := -272131/200000) 186 135
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t95 : ((507069619929/5000000000000 : ℚ) : ℝ) ≤ stT186 95 := by
  have hc : ((988461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507069619929/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((988461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c96 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-504323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2624243/5000000) (δ := 2333/250000000) (ψ := -272131/200000) 186 135
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t96 : ((-514773675633/10000000000000 : ℚ) : ℝ) ≤ stT186 96 := by
  have hc : ((-504373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-514773675633/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-504373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c97 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-633071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225631/400000) (δ := 4689/500000000) (ψ := -272131/200000) 186 136
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t97 : ((-642837507987/10000000000000 : ℚ) : ℝ) ≤ stT186 97 := by
  have hc : ((-633121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-642837507987/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-633121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c98 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((939851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871503/10000000) (δ := 377/40000000) (ψ := -272131/200000) 186 136
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t98 : ((118667732469/1250000000000 : ℚ) : ℝ) ≤ stT186 98 := by
  have hc : ((939801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118667732469/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((939801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c99 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((15523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3849363/10000000) (δ := 377/40000000) (ψ := -272131/200000) 186 136
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t99 : ((7788031713/2500000000000 : ℚ) : ℝ) ≤ stT186 99 := by
  have hc : ((7749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7788031713/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((7749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c100 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-60277/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -718521/1000000) (δ := 1897/200000000) (ψ := -272131/200000) 186 137
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t100 : ((-482241/5000000 : ℚ) : ℝ) ≤ stT186 100 := by
  have hc : ((-482241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482241/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-482241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c101 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((520543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1279137/5000000) (δ := 1897/200000000) (ψ := -272131/200000) 186 137
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t101 : ((517909793241/10000000000000 : ℚ) : ℝ) ≤ stT186 101 := by
  have hc : ((520493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517909793241/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((520493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c102 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((138013/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404609/2000000) (δ := 4659/500000000) (ψ := -272131/200000) 186 137
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t102 : ((136643256441/2000000000000 : ℚ) : ℝ) ≤ stT186 102 := by
  have hc : ((138003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136643256441/2000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((138003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c103 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-43447/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 409977/625000) (δ := 1897/200000000) (ψ := -272131/200000) 186 137
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t103 : ((-8562419167/100000000000 : ℚ) : ℝ) ≤ stT186 103 := by
  have hc : ((-86899/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8562419167/100000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-86899/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c104 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-57463/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1163887/2500000) (δ := 587/62500000) (ψ := -272131/200000) 186 138
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t104 : ((-56356931813/2000000000000 : ℚ) : ℝ) ≤ stT186 104 := by
  have hc : ((-57473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56356931813/2000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-57473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c105 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((124577/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -205731/10000000) (δ := 9411/1000000000) (ψ := -272131/200000) 186 138
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t105 : ((4862743797/50000000000 : ℚ) : ℝ) ≤ stT186 105 := by
  have hc : ((498283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4862743797/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((498283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c106 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-3429/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 840373/2000000) (δ := 587/62500000) (ψ := -272131/200000) 186 138
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t106 : ((-26656458627/2500000000000 : ℚ) : ℝ) ≤ stT186 106 := by
  have hc : ((-54889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26656458627/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-54889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c107 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-959477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7139841/10000000) (δ := 9499/1000000000) (ψ := -272131/200000) 186 139
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t107 : ((-927610253399/10000000000000 : ℚ) : ℝ) ≤ stT186 107 := by
  have hc : ((-959527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-927610253399/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-959527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c108 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((215277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112569/400000) (δ := 9499/1000000000) (ψ := -272131/200000) 186 139
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t108 : ((207126237/5000000000 : ℚ) : ℝ) ≤ stT186 108 := by
  have hc : ((53813/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207126237/5000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((53813/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c109 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((20793/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 735747/5000000) (δ := 9499/1000000000) (ψ := -272131/200000) 186 139
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t109 : ((39829757471/500000000000 : ℚ) : ℝ) ≤ stT186 109 := by
  have hc : ((83167/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39829757471/500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((83167/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c110 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-656709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2859053/5000000) (δ := 1163/125000000) (ψ := -272131/200000) 186 139
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t110 : ((-626195406417/10000000000000 : ℚ) : ℝ) ≤ stT186 110 := by
  have hc : ((-656759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626195406417/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-656759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c111 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-42229/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2890827/5000000) (δ := 2349/250000000) (ψ := -272131/200000) 186 140
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t111 : ((-160339837203/2500000000000 : ℚ) : ℝ) ≤ stT186 111 := by
  have hc : ((-337857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160339837203/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-337857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c112 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((799399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322251/2000000) (δ := 2349/250000000) (ψ := -272131/200000) 186 140
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t112 : ((755313662939/10000000000000 : ℚ) : ℝ) ≤ stT186 112 := by
  have hc : ((799349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((755313662939/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((799349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c113 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((532833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 252213/1000000) (δ := 2349/250000000) (ψ := -272131/200000) 186 140
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t113 : ((6264995297/125000000000 : ℚ) : ℝ) ≤ stT186 113 := by
  have hc : ((532783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6264995297/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((532783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c114 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-440229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6619059/10000000) (δ := 2349/250000000) (ψ := -272131/200000) 186 140
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t114 : ((-103083933211/1250000000000 : ℚ) : ℝ) ≤ stT186 114 := by
  have hc : ((-220127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103083933211/1250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-220127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c115 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-13319/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2513867/5000000) (δ := 9489/1000000000) (ψ := -272131/200000) 186 141
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t115 : ((-39748771629/1000000000000 : ℚ) : ℝ) ≤ stT186 115 := by
  have hc : ((-213129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39748771629/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-213129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c116 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((460393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -250441/2500000) (δ := 9489/1000000000) (ψ := -272131/200000) 186 141
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t116 : ((6678759987/78125000000 : ℚ) : ℝ) ≤ stT186 116 := by
  have hc : ((28773/31250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6678759987/78125000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((28773/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c117 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((183097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2989703/10000000) (δ := 9489/1000000000) (ψ := -272131/200000) 186 141
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t117 : ((10578129/312500000 : ℚ) : ℝ) ≤ stT186 117 := by
  have hc : ((5721/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10578129/312500000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((5721/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c118 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-186987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6947179/10000000) (δ := 4657/500000000) (ψ := -272131/200000) 186 141
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t118 : ((-6885790531/80000000000 : ℚ) : ℝ) ≤ stT186 118 := by
  have hc : ((-186997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6885790531/80000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-186997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c119 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-177961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2418371/5000000) (δ := 9421/1000000000) (ψ := -272131/200000) 186 142
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t119 : ((-81579794107/2500000000000 : ℚ) : ℝ) ≤ stT186 119 := by
  have hc : ((-88993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81579794107/2500000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-88993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c120 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((929333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945483/10000000) (δ := 4691/500000000) (ψ := -272131/200000) 186 142
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t120 : ((84831457221/1000000000000 : ℚ) : ℝ) ≤ stT186 120 := by
  have hc : ((929283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84831457221/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((929283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c121 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((197199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2913459/10000000) (δ := 4691/500000000) (ψ := -272131/200000) 186 142
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t121 : ((8962445583/250000000000 : ℚ) : ℝ) ≤ stT186 121 := by
  have hc : ((98587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8962445583/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((98587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c122 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-451233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3370321/5000000) (δ := 9421/1000000000) (ψ := -272131/200000) 186 142
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t122 : ((-102137510091/1250000000000 : ℚ) : ℝ) ≤ stT186 122 := by
  have hc : ((-225629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102137510091/1250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-225629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c123 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-477457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5171387/10000000) (δ := 583/62500000) (ψ := -272131/200000) 186 143
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t123 : ((-43055373669/1000000000000 : ℚ) : ℝ) ≤ stT186 123 := by
  have hc : ((-477507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43055373669/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-477507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c124 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((422969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406189/10000000) (δ := 583/62500000) (ψ := -272131/200000) 186 143
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t124 : ((5934604821/78125000000 : ℚ) : ℝ) ≤ stT186 124 := by
  have hc : ((13217/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5934604821/78125000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((13217/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c125 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((29831/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145549/625000) (δ := 583/62500000) (ψ := -272131/200000) 186 143
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t125 : ((53358831539/1000000000000 : ℚ) : ℝ) ≤ stT186 125 := by
  have hc : ((59657/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53358831539/1000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((59657/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c126 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-746511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6033997/10000000) (δ := 583/62500000) (ψ := -272131/200000) 186 143
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t126 : ((-665089544631/10000000000000 : ℚ) : ℝ) ≤ stT186 126 := by
  have hc : ((-746561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-665089544631/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-746561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c127 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-736879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1199619/2000000) (δ := 1171/125000000) (ψ := -272131/200000) 186 144
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t127 : ((-653919106653/10000000000000 : ℚ) : ℝ) ≤ stT186 127 := by
  have hc : ((-736929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653919106653/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-736929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c128 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((589463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2351007/10000000) (δ := 1171/125000000) (ψ := -272131/200000) 186 144
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t128 : ((520972130679/10000000000000 : ℚ) : ℝ) ≤ stT186 128 := by
  have hc : ((589413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((520972130679/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((589413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c129 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((874163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316929/2500000) (δ := 1171/125000000) (ψ := -272131/200000) 186 144
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t129 : ((15392255817/200000000000 : ℚ) : ℝ) ≤ stT186 129 := by
  have hc : ((874113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15392255817/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((874113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c130 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-182011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2429223/5000000) (δ := 1171/125000000) (ψ := -272131/200000) 186 144
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t130 : ((-39914078031/1250000000000 : ℚ) : ℝ) ≤ stT186 130 := by
  have hc : ((-45509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39914078031/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-45509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c131 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-974327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7286269/10000000) (δ := 473/50000000) (ψ := -272131/200000) 186 145
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t131 : ((-170263611357/2000000000000 : ℚ) : ℝ) ≤ stT186 131 := by
  have hc : ((-974377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170263611357/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-974377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c132 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((14137/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -375013/1000000) (δ := 473/50000000) (ψ := -272131/200000) 186 145
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t132 : ((3073992819/500000000000 : ℚ) : ℝ) ≤ stT186 132 := by
  have hc : ((14127/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3073992819/500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((14127/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c133 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((995369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120341/5000000) (δ := 473/50000000) (ψ := -272131/200000) 186 145
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t133 : ((863050062771/10000000000000 : ℚ) : ℝ) ≤ stT186 133 := by
  have hc : ((995319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((863050062771/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((995319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c134 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((270399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3242471/10000000) (δ := 18743/1000000000) (ψ := -272131/200000) 186 145
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t134 : ((58386462483/2500000000000 : ℚ) : ℝ) ≤ stT186 134 := by
  have hc : ((270349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58386462483/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((270349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c135 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-179059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3349861/5000000) (δ := 473/50000000) (ψ := -272131/200000) 186 145
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t135 : ((-154118062747/2000000000000 : ℚ) : ℝ) ≤ stT186 135 := by
  have hc : ((-179069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154118062747/2000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-179069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c136 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-3831/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2788247/5000000) (δ := 189/20000000) (ψ := -272131/200000) 186 146
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t136 : ((-52565178393/1000000000000 : ℚ) : ℝ) ≤ stT186 136 := by
  have hc : ((-61301/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52565178393/1000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-61301/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c137 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((646397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1084929/5000000) (δ := 9353/1000000000) (ψ := -272131/200000) 186 146
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t137 : ((552211083879/10000000000000 : ℚ) : ℝ) ≤ stT186 137 := by
  have hc : ((646347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((552211083879/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((646347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c138 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((442389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 302987/2500000) (δ := 189/20000000) (ψ := -272131/200000) 186 146
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t138 : ((11767656537/156250000000 : ℚ) : ℝ) ≤ stT186 138 := by
  have hc : ((110591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11767656537/156250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((110591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c139 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-12707/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4569387/10000000) (δ := 9353/1000000000) (ψ := -272131/200000) 186 146
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t139 : ((-21560116191/1000000000000 : ℚ) : ℝ) ≤ stT186 139 := by
  have hc : ((-25419/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21560116191/1000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-25419/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c140 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-99981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -975653/1250000) (δ := 4723/500000000) (ψ := -272131/200000) 186 147
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t140 : ((-8450366783/100000000000 : ℚ) : ℝ) ≤ stT186 140 := by
  have hc : ((-49993/50000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8450366783/100000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-49993/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c141 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-225501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4495633/10000000) (δ := 4723/500000000) (ψ := -272131/200000) 186 147
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t141 : ((-23743528219/1250000000000 : ℚ) : ℝ) ≤ stT186 141 := by
  have hc : ((-225551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23743528219/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-225551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c142 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((177051/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241877/2000000) (δ := 4723/500000000) (ψ := -272131/200000) 186 147
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t142 : ((148569443421/2000000000000 : ℚ) : ℝ) ≤ stT186 142 := by
  have hc : ((177041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148569443421/2000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((177041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c143 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((681109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2053799/10000000) (δ := 4723/500000000) (ψ := -272131/200000) 186 147
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t143 : ((284765070139/5000000000000 : ℚ) : ℝ) ≤ stT186 143 := by
  have hc : ((681059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284765070139/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((681059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c144 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-520027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2647099/5000000) (δ := 4723/500000000) (ψ := -272131/200000) 186 147
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t144 : ((-216698923359/5000000000000 : ℚ) : ℝ) ≤ stT186 144 := by
  have hc : ((-520077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-216698923359/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-520077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c145 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-30173/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1798933/2500000) (δ := 1183/125000000) (ψ := -272131/200000) 186 148
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t145 : ((-80187572163/1000000000000 : ℚ) : ℝ) ≤ stT186 145 := by
  have hc : ((-482793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80187572163/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-482793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c146 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-29133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1999917/5000000) (δ := 9339/1000000000) (ψ := -272131/200000) 186 148
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t146 : ((-12076012949/5000000000000 : ℚ) : ℝ) ≤ stT186 146 := by
  have hc : ((-29183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12076012949/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-29183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c147 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((47297/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82579/1000000) (δ := 1183/125000000) (ψ := -272131/200000) 186 148
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t147 : ((39007841477/500000000000 : ℚ) : ℝ) ≤ stT186 147 := by
  have hc : ((94589/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39007841477/500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((94589/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c148 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((298633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232677/1000000) (δ := 9339/1000000000) (ψ := -272131/200000) 186 148
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t148 : ((7670437011/156250000000 : ℚ) : ℝ) ≤ stT186 148 := by
  have hc : ((18663/31250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7670437011/156250000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((18663/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c149 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-287439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5458127/10000000) (δ := 1183/125000000) (ψ := -272131/200000) 186 148
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t149 : ((-919920733/19531250000 : ℚ) : ℝ) ≤ stT186 149 := by
  have hc : ((-35933/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-919920733/19531250000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-35933/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c150 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-479719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3569749/5000000) (δ := 9371/1000000000) (ψ := -272131/200000) 186 149
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t150 : ((-765057689/9765625000 : ℚ) : ℝ) ≤ stT186 150 := by
  have hc : ((-14992/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-765057689/9765625000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-14992/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c151 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-767/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4049759/10000000) (δ := 9371/1000000000) (ψ := -272131/200000) 186 149
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t151 : ((-19993981941/5000000000000 : ℚ) : ℝ) ≤ stT186 151 := by
  have hc : ((-24569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19993981941/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-24569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c152 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((11551/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -490217/5000000) (δ := 1179/125000000) (ψ := -272131/200000) 186 149
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t152 : ((74948720121/1000000000000 : ℚ) : ℝ) ≤ stT186 152 := by
  have hc : ((92403/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74948720121/1000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((92403/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c153 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((169179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2068757/10000000) (δ := 1179/125000000) (ψ := -272131/200000) 186 149
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t153 : ((68381497629/1250000000000 : ℚ) : ℝ) ≤ stT186 153 := by
  have hc : ((338333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68381497629/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((338333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c154 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-56437/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5098093/10000000) (δ := 9371/1000000000) (ψ := -272131/200000) 186 149
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t154 : ((-181933076179/5000000000000 : ℚ) : ℝ) ≤ stT186 154 := by
  have hc : ((-225773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181933076179/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-225773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c155 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-19897/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3800079/5000000) (δ := 373/40000000) (ψ := -272131/200000) 186 150
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t155 : ((-399561789/5000000000 : ℚ) : ℝ) ≤ stT186 155 := by
  have hc : ((-9949/10000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-399561789/5000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-9949/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c156 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-33717/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4609789/10000000) (δ := 4739/500000000) (ψ := -272131/200000) 186 150
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t156 : ((-108000866413/5000000000000 : ℚ) : ℝ) ≤ stT186 156 := by
  have hc : ((-134893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108000866413/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-134893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c157 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((198199/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409633/2500000) (δ := 4739/500000000) (ψ := -272131/200000) 186 150
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t157 : ((158169871039/2500000000000 : ℚ) : ℝ) ≤ stT186 157 := by
  have hc : ((396373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158169871039/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((396373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c158 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((432527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 656923/5000000) (δ := 4739/500000000) (ψ := -272131/200000) 186 150
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t158 : ((172039996807/2500000000000 : ℚ) : ℝ) ≤ stT186 158 := by
  have hc : ((216251/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172039996807/2500000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((216251/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c159 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-63951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530953/1250000) (δ := 4739/500000000) (ψ := -272131/200000) 186 150
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t159 : ((-1585509211/156250000000 : ℚ) : ℝ) ≤ stT186 159 := by
  have hc : ((-7997/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1585509211/156250000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-7997/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c160 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-192409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1790747/2500000) (δ := 4739/500000000) (ψ := -272131/200000) 186 150
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t160 : ((-15212068883/200000000000 : ℚ) : ℝ) ≤ stT186 160 := by
  have hc : ((-192419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15212068883/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-192419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c161 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-635241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5647793/10000000) (δ := 4693/500000000) (ψ := -272131/200000) 186 151
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t161 : ((-500679825301/10000000000000 : ℚ) : ℝ) ≤ stT186 161 := by
  have hc : ((-635291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500679825301/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-635291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c162 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((55873/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2768513/10000000) (δ := 4693/500000000) (ψ := -272131/200000) 186 151
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t162 : ((87786105879/2500000000000 : ℚ) : ℝ) ≤ stT186 162 := by
  have hc : ((223467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87786105879/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((223467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c163 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((999307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1861/200000) (δ := 9417/1000000000) (ψ := -272131/200000) 186 151
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t163 : ((39133901891/500000000000 : ℚ) : ℝ) ≤ stT186 163 := by
  have hc : ((999257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39133901891/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((999257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c164 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((385697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2937083/10000000) (δ := 9417/1000000000) (ψ := -272131/200000) 186 151
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t164 : ((75284850399/2500000000000 : ℚ) : ℝ) ≤ stT186 164 := by
  have hc : ((385647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75284850399/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((385647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c165 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-670387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2881909/5000000) (δ := 9417/1000000000) (ψ := -272131/200000) 186 151
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t165 : ((-521934534063/10000000000000 : ℚ) : ℝ) ≤ stT186 165 := by
  have hc : ((-670437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521934534063/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-670437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c166 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-95887/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -285379/400000) (δ := 9493/1000000000) (ψ := -272131/200000) 186 152
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t166 : ((-18606667923/250000000000 : ℚ) : ℝ) ≤ stT186 166 := by
  have hc : ((-23973/25000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18606667923/250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-23973/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c167 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-1651/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4341639/10000000) (δ := 931/100000000) (ψ := -272131/200000) 186 152
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t167 : ((-39936573/3125000000 : ℚ) : ℝ) ≤ stT186 167 := by
  have hc : ((-3303/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39936573/3125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-3303/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c168 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((810251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782771/5000000) (δ := 9493/1000000000) (ψ := -272131/200000) 186 152
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t168 : ((156270758679/2500000000000 : ℚ) : ℝ) ≤ stT186 168 := by
  have hc : ((810201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156270758679/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((810201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c169 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((35523/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59707/500000) (δ := 9493/1000000000) (ψ := -272131/200000) 186 152
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t169 : ((2732381883/40000000000 : ℚ) : ℝ) ≤ stT186 169 := by
  have hc : ((35521/40000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2732381883/40000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((35521/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c170 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-1051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63/160) (δ := 931/100000000) (ψ := -272131/200000) 186 152
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t170 : ((-326266911/1000000000000 : ℚ) : ℝ) ≤ stT186 170 := by
  have hc : ((-2127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-326266911/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-2127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c171 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-44449/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1666193/2500000) (δ := 9493/1000000000) (ψ := -272131/200000) 186 152
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t171 : ((-849823777/12500000000 : ℚ) : ℝ) ≤ stT186 171 := by
  have hc : ((-88903/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-849823777/12500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-88903/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c172 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-820299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6331823/10000000) (δ := 47/5000000) (ψ := -272131/200000) 186 153
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t172 : ((-625510370057/10000000000000 : ℚ) : ℝ) ≤ stT186 172 := by
  have hc : ((-820349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625510370057/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-820349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c173 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((23213/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -909043/2500000) (δ := 9403/1000000000) (ψ := -272131/200000) 186 153
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t173 : ((3528178571/400000000000 : ℚ) : ℝ) ≤ stT186 173 := by
  have hc : ((23203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3528178571/400000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((23203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c174 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((231941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -956051/10000000) (δ := 47/5000000) (ψ := -272131/200000) 186 153
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t174 : ((175824531993/2500000000000 : ℚ) : ℝ) ≤ stT186 174 := by
  have hc : ((463857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175824531993/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((463857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c175 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((387687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427181/2500000) (δ := 9403/1000000000) (ψ := -272131/200000) 186 153
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t175 : ((18315285021/312500000000 : ℚ) : ℝ) ≤ stT186 175 := by
  have hc : ((193831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18315285021/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((193831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c176 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-171667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2179147/5000000) (δ := 9403/1000000000) (ψ := -272131/200000) 186 153
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t176 : ((-129436668543/10000000000000 : ℚ) : ℝ) ≤ stT186 176 := by
  have hc : ((-171717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129436668543/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-171717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c177 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-470633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6992891/10000000) (δ := 9403/1000000000) (ψ := -272131/200000) 186 153
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t177 : ((-176884336863/2500000000000 : ℚ) : ℝ) ≤ stT186 177 := by
  have hc : ((-235329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176884336863/2500000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-235329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c178 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-152523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1219071/2000000) (δ := 9307/1000000000) (ψ := -272131/200000) 186 154
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t178 : ((-28582091139/500000000000 : ℚ) : ℝ) ≤ stT186 178 := by
  have hc : ((-152533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28582091139/500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-152533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c179 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((34759/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1745143/5000000) (δ := 1187/125000000) (ψ := -272131/200000) 186 154
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t179 : ((5194523763/400000000000 : ℚ) : ℝ) ≤ stT186 179 := by
  have hc : ((34749/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5194523763/400000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((34749/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c180 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((935929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -899771/10000000) (δ := 1187/125000000) (ψ := -272131/200000) 186 154
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t180 : ((139512418409/2000000000000 : ℚ) : ℝ) ≤ stT186 180 := by
  have hc : ((935879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139512418409/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((935879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c181 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((195867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 838211/5000000) (δ := 1187/125000000) (ψ := -272131/200000) 186 154
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t181 : ((145577474723/2500000000000 : ℚ) : ℝ) ≤ stT186 181 := by
  have hc : ((391709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145577474723/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((391709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c182 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-31059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2119193/5000000) (δ := 1187/125000000) (ψ := -272131/200000) 186 154
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t182 : ((-36850799/4000000000 : ℚ) : ℝ) ≤ stT186 182 := by
  have hc : ((-62143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36850799/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-62143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c183 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-910191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3393177/5000000) (δ := 9307/1000000000) (ψ := -272131/200000) 186 154
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t183 : ((-336435086251/5000000000000 : ℚ) : ℝ) ≤ stT186 183 := by
  have hc : ((-910241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336435086251/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-910241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c184 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-416421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1277509/2000000) (δ := 4707/500000000) (ψ := -272131/200000) 186 155
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t184 : ((-15350407783/250000000000 : ℚ) : ℝ) ≤ stT186 184 := by
  have hc : ((-208223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15350407783/250000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-208223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c185 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((11957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3867199/10000000) (δ := 9389/1000000000) (ψ := -272131/200000) 186 155
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t185 : ((1096571681/625000000000 : ℚ) : ℝ) ≤ stT186 185 := by
  have hc : ((2983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1096571681/625000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((2983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c186 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((855547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1360477/10000000) (δ := 9389/1000000000) (ψ := -272131/200000) 186 155
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t186 : ((125456068559/2000000000000 : ℚ) : ℝ) ≤ stT186 186 := by
  have hc : ((855497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125456068559/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((855497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c187 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((224769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1132853/10000000) (δ := 9389/1000000000) (ψ := -272131/200000) 186 155
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t187 : ((41089533817/625000000000 : ℚ) : ℝ) ≤ stT186 187 := by
  have hc : ((449513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41089533817/625000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((449513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c188 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((125331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1806419/5000000) (δ := 4707/500000000) (ψ := -272131/200000) 186 155
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t188 : ((22842610011/2500000000000 : ℚ) : ℝ) ≤ stT186 188 := by
  have hc : ((125281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22842610011/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((125281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c189 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-758551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6079709/10000000) (δ := 9389/1000000000) (ψ := -272131/200000) 186 155
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t189 : ((-551801057193/10000000000000 : ℚ) : ℝ) ≤ stT186 189 := by
  have hc : ((-758601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551801057193/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-758601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c190 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-481643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7174449/10000000) (δ := 4661/500000000) (ψ := -272131/200000) 186 156
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t190 : ((-87359763909/1250000000000 : ℚ) : ℝ) ≤ stT186 190 := by
  have hc : ((-120417/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87359763909/1250000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-120417/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c191 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-317029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2366739/5000000) (δ := 4661/500000000) (ψ := -272131/200000) 186 156
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t191 : ((-9177217497/400000000000 : ℚ) : ℝ) ≤ stT186 191 := by
  have hc : ((-317079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9177217497/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-317079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c192 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((302067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461059/2000000) (δ := 9481/1000000000) (ψ := -272131/200000) 186 156
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t192 : ((108989892427/2500000000000 : ℚ) : ℝ) ≤ stT186 192 := by
  have hc : ((151021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108989892427/2500000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((151021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c193 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((999027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110287/10000000) (δ := 9481/1000000000) (ψ := -272131/200000) 186 156
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t193 : ((143815725851/2000000000000 : ℚ) : ℝ) ≤ stT186 193 := by
  have hc : ((998977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143815725851/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((998977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c194 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((267891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2513407/10000000) (δ := 9481/1000000000) (ψ := -272131/200000) 186 156
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t194 : ((48079134407/1250000000000 : ℚ) : ℝ) ≤ stT186 194 := by
  have hc : ((133933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48079134407/1250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((133933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c195 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-38099/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2452079/5000000) (δ := 9481/1000000000) (ψ := -272131/200000) 186 156
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t195 : ((-682171149/25000000000 : ℚ) : ℝ) ≤ stT186 195 := by
  have hc : ((-4763/12500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682171149/25000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-4763/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c196 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-974003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182067/250000) (δ := 4661/500000000) (ψ := -272131/200000) 186 156
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t196 : ((-347876210579/5000000000000 : ℚ) : ℝ) ≤ stT186 196 := by
  have hc : ((-974053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347876210579/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-974053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c197 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-753089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1514713/2500000) (δ := 4687/500000000) (ψ := -272131/200000) 186 157
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t197 : ((-536589696469/10000000000000 : ℚ) : ℝ) ≤ stT186 197 := by
  have hc : ((-753139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536589696469/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-753139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c198 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((5557/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3704417/10000000) (δ := 9429/1000000000) (ψ := -272131/200000) 186 157
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t198 : ((31575734339/5000000000000 : ℚ) : ℝ) ≤ stT186 198 := by
  have hc : ((44431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31575734339/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((44431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c199 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((26727/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17023/125000) (δ := 9429/1000000000) (ψ := -272131/200000) 186 157
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t199 : ((303122477767/5000000000000 : ℚ) : ℝ) ≤ stT186 199 := by
  have hc : ((427607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303122477767/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((427607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c200 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((925823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242243/2500000) (δ := 4687/500000000) (ψ := -272131/200000) 186 157
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t200 : ((327309821469/5000000000000 : ℚ) : ℝ) ≤ stT186 200 := by
  have hc : ((925773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327309821469/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((925773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c201 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((252743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1644103/5000000) (δ := 4687/500000000) (ψ := -272131/200000) 186 157
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t201 : ((35647148817/2000000000000 : ℚ) : ℝ) ≤ stT186 201 := by
  have hc : ((252693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35647148817/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((252693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c202 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-619063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2797931/5000000) (δ := 9429/1000000000) (ψ := -272131/200000) 186 157
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t202 : ((-217803334287/5000000000000 : ℚ) : ℝ) ≤ stT186 202 := by
  have hc : ((-619113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217803334287/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-619113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c203 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-999883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488487/625000) (δ := 1167/125000000) (ψ := -272131/200000) 186 158
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t203 : ((-701815975179/10000000000000 : ℚ) : ℝ) ≤ stT186 203 := by
  have hc : ((-999933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-701815975179/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-999933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c204 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-598411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2765391/5000000) (δ := 1167/125000000) (ψ := -272131/200000) 186 158
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t204 : ((-419007083001/10000000000000 : ℚ) : ℝ) ≤ stT186 204 := by
  have hc : ((-598461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419007083001/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-598461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c205 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((132413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -814233/2500000) (δ := 1167/125000000) (ψ := -272131/200000) 186 158
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t205 : ((2311593771/125000000000 : ℚ) : ℝ) ≤ stT186 205 := by
  have hc : ((33097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2311593771/125000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((33097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c206 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((92197/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -994149/10000000) (δ := 1167/125000000) (ψ := -272131/200000) 186 158
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t206 : ((2007287773/31250000000 : ℚ) : ℝ) ≤ stT186 206 := by
  have hc : ((2881/3125 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2007287773/31250000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((2881/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c207 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((876109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62883/500000) (δ := 1167/125000000) (ψ := -272131/200000) 186 158
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t207 : ((76112881979/1250000000000 : ℚ) : ℝ) ≤ stT186 207 := by
  have hc : ((876059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76112881979/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((876059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c208 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((85253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1749317/5000000) (δ := 9467/1000000000) (ψ := -272131/200000) 186 158
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t208 : ((118189929/10000000000 : ℚ) : ℝ) ≤ stT186 208 := by
  have hc : ((21307/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118189929/10000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((21307/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c209 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-659949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5728867/10000000) (δ := 9467/1000000000) (ψ := -272131/200000) 186 158
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t209 : ((-91306241657/2000000000000 : ℚ) : ℝ) ≤ stT186 209 := by
  have hc : ((-659999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91306241657/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-659999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c210 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-499643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7759511/10000000) (δ := 9443/1000000000) (ψ := -272131/200000) 186 159
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t210 : ((-43100487261/625000000000 : ℚ) : ℝ) ≤ stT186 210 := by
  have hc : ((-124917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43100487261/625000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-124917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c211 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-302353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2775241/5000000) (δ := 9443/1000000000) (ψ := -272131/200000) 186 159
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t211 : ((-104082892081/2500000000000 : ℚ) : ℝ) ≤ stT186 211 := by
  have hc : ((-151189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104082892081/2500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-151189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c212 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((228007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837979/2500000) (δ := 117/12500000) (ψ := -272131/200000) 186 159
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t212 : ((78280661757/5000000000000 : ℚ) : ℝ) ≤ stT186 212 := by
  have hc : ((227957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78280661757/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((227957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c213 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((893611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145459/1250000) (δ := 9443/1000000000) (ψ := -272131/200000) 186 159
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t213 : ((153064318617/2500000000000 : ℚ) : ℝ) ≤ stT186 213 := by
  have hc : ((893561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153064318617/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((893561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c214 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((229703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1014341/10000000) (δ := 117/12500000) (ψ := -272131/200000) 186 159
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t214 : ((62805192177/1000000000000 : ℚ) : ℝ) ≤ stT186 214 := by
  have hc : ((459381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62805192177/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((459381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c215 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((14677/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3182171/10000000) (δ := 117/12500000) (ψ := -272131/200000) 186 159
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t215 : ((10007920953/500000000000 : ℚ) : ℝ) ≤ stT186 215 := by
  have hc : ((29349/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10007920953/500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((29349/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c216 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-535573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5339957/10000000) (δ := 117/12500000) (ψ := -272131/200000) 186 159
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t216 : ((-182222693961/5000000000000 : ℚ) : ℝ) ≤ stT186 216 := by
  have hc : ((-535623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182222693961/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-535623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c217 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-989289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3743873/5000000) (δ := 9443/1000000000) (ψ := -272131/200000) 186 159
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t217 : ((-134321566691/2000000000000 : ℚ) : ℝ) ≤ stT186 217 := by
  have hc : ((-989339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134321566691/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-989339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c218 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-759223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6082287/10000000) (δ := 187/20000000) (ψ := -272131/200000) 186 160
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t218 : ((-257122486539/5000000000000 : ℚ) : ℝ) ≤ stT186 218 := by
  have hc : ((-759273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257122486539/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-759273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c219 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-2713/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1977061/5000000) (δ := 9453/1000000000) (ψ := -272131/200000) 186 160
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t219 : ((-1841723919/2500000000000 : ℚ) : ℝ) ≤ stT186 219 := by
  have hc : ((-5451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1841723919/2500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-5451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c220 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((9279/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73427/400000) (δ := 9453/1000000000) (ψ := -272131/200000) 186 160
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t220 : ((50043769173/1000000000000 : ℚ) : ℝ) ≤ stT186 220 := by
  have hc : ((74227/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50043769173/1000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((74227/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c221 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((198807/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273193/10000000) (δ := 9453/1000000000) (ψ := -272131/200000) 186 160
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t221 : ((4178911737/62500000000 : ℚ) : ℝ) ≤ stT186 221 := by
  have hc : ((198797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4178911737/62500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((198797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c222 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((291251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1186241/5000000) (δ := 9453/1000000000) (ψ := -272131/200000) 186 160
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t222 : ((24432259657/625000000000 : ℚ) : ℝ) ≤ stT186 222 := by
  have hc : ((145613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24432259657/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((145613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c223 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-106261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2231189/5000000) (δ := 9453/1000000000) (ψ := -272131/200000) 186 160
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t223 : ((-711744199/50000000000 : ℚ) : ℝ) ≤ stT186 223 := by
  have hc : ((-53143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-711744199/50000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-53143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c224 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-432807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 408933/625000) (δ := 187/20000000) (ψ := -272131/200000) 186 160
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t224 : ((-2259362751/39062500000 : ℚ) : ℝ) ≤ stT186 224 := by
  have hc : ((-13526/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2259362751/39062500000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-13526/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c225 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-477059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7093739/10000000) (δ := 9457/1000000000) (ψ := -272131/200000) 186 161
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t225 : ((-79514039757/1250000000000 : ℚ) : ℝ) ≤ stT186 225 := by
  have hc : ((-119271/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79514039757/1250000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-119271/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c226 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-213817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2515837/5000000) (δ := 9373/500000000) (ψ := -272131/200000) 186 161
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t226 : ((-71122886911/2500000000000 : ℚ) : ℝ) ≤ stT186 226 := by
  have hc : ((-106921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71122886911/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-106921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c227 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((74059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119147/400000) (δ := 9457/1000000000) (ψ := -272131/200000) 186 161
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t227 : ((49148024427/2000000000000 : ℚ) : ℝ) ≤ stT186 227 := by
  have hc : ((74049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49148024427/2000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((74049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c228 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((465457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -934721/10000000) (δ := 9457/1000000000) (ψ := -272131/200000) 186 161
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t228 : ((19264986807/312500000000 : ℚ) : ℝ) ≤ stT186 228 := by
  have hc : ((58179/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19264986807/312500000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((58179/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c229 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((9047/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 220061/2000000) (δ := 9457/1000000000) (ψ := -272131/200000) 186 161
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t229 : ((5978090037/100000000000 : ℚ) : ℝ) ≤ stT186 229 := by
  have hc : ((18093/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5978090037/100000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((18093/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c230 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((78693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3126449/10000000) (δ := 4673/500000000) (ψ := -272131/200000) 186 161
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t230 : ((5188034809/250000000000 : ℚ) : ℝ) ≤ stT186 230 := by
  have hc : ((157361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5188034809/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((157361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c231 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-233867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1028761/2000000) (δ := 4673/500000000) (ψ := -272131/200000) 186 161
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t231 : ((-1202263353/39062500000 : ℚ) : ℝ) ≤ stT186 231 := by
  have hc : ((-58473/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1202263353/39062500000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-58473/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c232 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-960883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7152419/10000000) (δ := 4673/500000000) (ψ := -272131/200000) 186 161
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t232 : ((-630884225289/10000000000000 : ℚ) : ℝ) ≤ stT186 232 := by
  have hc : ((-960933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-630884225289/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-960933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c233 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-868127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6555533/10000000) (δ := 4719/500000000) (ψ := -272131/200000) 186 162
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t233 : ((-284380926297/5000000000000 : ℚ) : ℝ) ≤ stT186 233 := by
  have hc : ((-868177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284380926297/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-868177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c234 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-50417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4564077/10000000) (δ := 1873/200000000) (ψ := -272131/200000) 186 162
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t234 : ((-32965188867/2000000000000 : ℚ) : ℝ) ≤ stT186 234 := by
  have hc : ((-50427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32965188867/2000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-50427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c235 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((102543/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2581131/10000000) (δ := 1873/200000000) (ψ := -272131/200000) 186 162
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t235 : ((8360643353/250000000000 : ℚ) : ℝ) ≤ stT186 235 := by
  have hc : ((102533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8360643353/250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((102533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c236 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((970707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303301/5000000) (δ := 4719/500000000) (ψ := -272131/200000) 186 162
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t236 : ((9872552347/156250000000 : ℚ) : ℝ) ≤ stT186 236 := by
  have hc : ((970657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9872552347/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((970657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c237 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((855737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 679779/5000000) (δ := 1873/200000000) (ψ := -272131/200000) 186 162
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t237 : ((555827748903/10000000000000 : ℚ) : ℝ) ≤ stT186 237 := by
  have hc : ((855687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555827748903/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((855687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c238 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((60353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10367/31250) (δ := 4719/500000000) (ψ := -272131/200000) 186 162
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t238 : ((78225786243/5000000000000 : ℚ) : ℝ) ≤ stT186 238 := by
  have hc : ((120681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78225786243/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((120681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c239 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-15961/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5267139/10000000) (δ := 1873/200000000) (ψ := -272131/200000) 186 162
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t239 : ((-165205370647/5000000000000 : ℚ) : ℝ) ≤ stT186 239 := by
  have hc : ((-255401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165205370647/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-255401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c240 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-966873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72087/100000) (δ := 1873/200000000) (ψ := -272131/200000) 186 162
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t240 : ((-312073431327/5000000000000 : ℚ) : ℝ) ≤ stT186 240 := by
  have hc : ((-966923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312073431327/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-966923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c241 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-870157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6565793/10000000) (δ := 37/3906250) (ψ := -272131/200000) 186 163
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t241 : ((-560549930499/10000000000000 : ℚ) : ℝ) ≤ stT186 241 := by
  have hc : ((-870207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560549930499/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-870207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c242 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-70369/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4640321/10000000) (δ := 37/3906250) (ψ := -272131/200000) 186 163
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t242 : ((-3619439019/200000000000 : ℚ) : ℝ) ≤ stT186 242 := by
  have hc : ((-140763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3619439019/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-140763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c243 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((92653/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2722801/10000000) (δ := 9331/1000000000) (ψ := -272131/200000) 186 163
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t243 : ((118860969/4000000000 : ℚ) : ℝ) ≤ stT186 243 := by
  have hc : ((92643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118860969/4000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((92643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c244 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((947569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -813139/10000000) (δ := 9331/1000000000) (ψ := -272131/200000) 186 163
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t244 : ((75823312937/1250000000000 : ℚ) : ℝ) ≤ stT186 244 := by
  have hc : ((947519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75823312937/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((947519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c245 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((90667/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68043/625000) (δ := 1167/62500000) (ψ := -272131/200000) 186 163
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t245 : ((7240221989/125000000000 : ℚ) : ℝ) ≤ stT186 245 := by
  have hc : ((45331/50000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7240221989/125000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((45331/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c246 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((368763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 745699/2500000) (δ := 37/3906250) (ψ := -272131/200000) 186 163
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t246 : ((29385319961/1250000000000 : ℚ) : ℝ) ≤ stT186 246 := by
  have hc : ((368713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29385319961/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((368713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c247 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-92007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608651/1250000) (δ := 37/3906250) (ψ := -272131/200000) 186 163
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t247 : ((-23420251023/1000000000000 : ℚ) : ℝ) ≤ stT186 247 := by
  have hc : ((-184039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23420251023/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-184039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c248 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-903729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3373997/5000000) (δ := 37/3906250) (ψ := -272131/200000) 186 163
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t248 : ((-573900568779/10000000000000 : ℚ) : ℝ) ≤ stT186 248 := by
  have hc : ((-903779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573900568779/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-903779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c249 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-11919/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7088763/10000000) (δ := 9379/1000000000) (ψ := -272131/200000) 186 164
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t249 : ((-2417204593/40000000000 : ℚ) : ℝ) ≤ stT186 249 := by
  have hc : ((-95357/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2417204593/40000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-95357/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c250 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-124047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5224997/10000000) (δ := 589/62500000) (ψ := -272131/200000) 186 164
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t250 : ((-19615543783/625000000000 : ℚ) : ℝ) ≤ stT186 250 := by
  have hc : ((-248119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19615543783/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-248119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c251 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((110729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3368717/10000000) (δ := 589/62500000) (ψ := -272131/200000) 186 164
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t251 : ((2183615643/156250000000 : ℚ) : ℝ) ≤ stT186 251 := by
  have hc : ((6919/31250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2183615643/156250000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((6919/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c252 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((820831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151983/1000000) (δ := 9379/1000000000) (ψ := -272131/200000) 186 164
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t252 : ((25852139157/500000000000 : ℚ) : ℝ) ≤ stT186 252 := by
  have hc : ((820781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25852139157/500000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((820781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c253 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((991729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80439/2500000) (δ := 9379/1000000000) (ψ := -272131/200000) 186 164
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t253 : ((311731318613/5000000000000 : ℚ) : ℝ) ≤ stT186 253 := by
  have hc : ((991679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311731318613/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((991679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c254 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((65059/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269511/1250000) (δ := 9379/1000000000) (ψ := -272131/200000) 186 164
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t254 : ((4081845757/100000000000 : ℚ) : ℝ) ≤ stT186 254 := by
  have hc : ((32527/50000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4081845757/100000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((32527/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c255 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-22487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 995803/2500000) (δ := 589/62500000) (ψ := -272131/200000) 186 164
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t255 : ((-564529313/400000000000 : ℚ) : ℝ) ≤ stT186 255 := by
  have hc : ((-22537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564529313/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-22537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c256 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-340993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725397/1250000) (δ := 9379/1000000000) (ψ := -272131/200000) 186 164
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t256 : ((-106568295509/2500000000000 : ℚ) : ℝ) ≤ stT186 256 := by
  have hc : ((-170509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106568295509/2500000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-170509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c257 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-497737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304641/400000) (δ := 9379/1000000000) (ψ := -272131/200000) 186 164
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t257 : ((-155247736823/2500000000000 : ℚ) : ℝ) ≤ stT186 257 := by
  have hc : ((-248881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155247736823/2500000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-248881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c258 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-101213/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6286111/10000000) (δ := 9317/1000000000) (ψ := -272131/200000) 186 165
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t258 : ((-252065488521/5000000000000 : ℚ) : ℝ) ≤ stT186 258 := by
  have hc : ((-404877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252065488521/5000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-404877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c259 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-55559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2243629/5000000) (δ := 4743/500000000) (ψ := -272131/200000) 186 165
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t259 : ((-6906092591/500000000000 : ℚ) : ℝ) ≤ stT186 259 := by
  have hc : ((-111143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6906092591/500000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-111143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c260 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((236487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1347667/5000000) (δ := 4743/500000000) (ψ := -272131/200000) 186 165
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t260 : ((73323673963/2500000000000 : ℚ) : ℝ) ≤ stT186 260 := by
  have hc : ((118231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73323673963/2500000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((118231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c261 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((934439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227573/2500000) (δ := 4743/500000000) (ψ := -272131/200000) 186 165
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t261 : ((72296480097/1250000000000 : ℚ) : ℝ) ≤ stT186 261 := by
  have hc : ((934389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72296480097/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((934389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c262 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((940341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 433957/5000000) (δ := 27917/1000000000) (ψ := -272131/200000) 186 165
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t262 : ((290456830191/5000000000000 : ℚ) : ℝ) ≤ stT186 262 := by
  have hc : ((940291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290456830191/5000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((940291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c263 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((49259/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 659833/2500000) (δ := 4743/500000000) (ψ := -272131/200000) 186 165
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t263 : ((7592824251/250000000000 : ℚ) : ℝ) ≤ stT186 263 := by
  have hc : ((24627/50000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7592824251/250000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((24627/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c264 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-189669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4404053/10000000) (δ := 27917/1000000000) (ψ := -272131/200000) 186 165
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t264 : ((-58382038151/5000000000000 : ℚ) : ℝ) ≤ stT186 264 := by
  have hc : ((-189719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58382038151/5000000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-189719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c265 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-155921/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6162079/10000000) (δ := 4743/500000000) (ψ := -272131/200000) 186 165
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t265 : ((-11973473697/250000000000 : ℚ) : ℝ) ≤ stT186 265 := by
  have hc : ((-155931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11973473697/250000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-155931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c266 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-999717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3897231/5000000) (δ := 9393/1000000000) (ψ := -272131/200000) 186 166
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t266 : ((-30649856919/500000000000 : ℚ) : ℝ) ≤ stT186 266 := by
  have hc : ((-999767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30649856919/500000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-999767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c267 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-37533/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6049643/10000000) (δ := 941/100000000) (ψ := -272131/200000) 186 166
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t267 : ((-45942776361/1000000000000 : ℚ) : ℝ) ≤ stT186 267 := by
  have hc : ((-75071/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45942776361/1000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-75071/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c268 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-38283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4311333/10000000) (δ := 9393/1000000000) (ψ := -272131/200000) 186 166
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t268 : ((-1462045599/156250000000 : ℚ) : ℝ) ≤ stT186 268 := by
  have hc : ((-76591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1462045599/156250000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-76591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c269 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((513279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2579487/10000000) (δ := 9393/1000000000) (ψ := -272131/200000) 186 166
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t269 : ((31292085359/1000000000000 : ℚ) : ℝ) ≤ stT186 269 := by
  have hc : ((513229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31292085359/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((513229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c270 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((235553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -427029/5000000) (δ := 9393/1000000000) (ψ := -272131/200000) 186 166
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t270 : ((14334523749/250000000000 : ℚ) : ℝ) ≤ stT186 270 := by
  have hc : ((471081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14334523749/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((471081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c271 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((940737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173/2000) (δ := 941/100000000) (ψ := -272131/200000) 186 166
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t271 : ((17857061321/312500000000 : ℚ) : ℝ) ≤ stT186 271 := by
  have hc : ((940687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17857061321/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((940687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c272 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((513897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322211/1250000) (δ := 941/100000000) (ψ := -272131/200000) 186 166
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t272 : ((311565476133/10000000000000 : ℚ) : ℝ) ≤ stT186 272 := by
  have hc : ((513847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311565476133/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((513847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c273 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-71179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4284099/10000000) (δ := 9393/1000000000) (ψ := -272131/200000) 186 166
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t273 : ((-2693415907/312500000000 : ℚ) : ℝ) ≤ stT186 273 := by
  have hc : ((-17801/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2693415907/312500000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-17801/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c274 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-91643/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239373/400000) (δ := 9393/1000000000) (ψ := -272131/200000) 186 166
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t274 : ((-221469679431/5000000000000 : ℚ) : ℝ) ≤ stT186 274 := by
  have hc : ((-366597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221469679431/5000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-366597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c275 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-997531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7678273/10000000) (δ := 941/100000000) (ψ := -272131/200000) 186 166
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t275 : ((-601564287363/10000000000000 : ℚ) : ℝ) ≤ stT186 275 := by
  have hc : ((-997581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-601564287363/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-997581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c276 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-411291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6341833/10000000) (δ := 9303/1000000000) (ψ := -272131/200000) 186 167
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t276 : ((-6189585997/125000000000 : ℚ) : ℝ) ≤ stT186 276 := by
  have hc : ((-102829/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6189585997/125000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-102829/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c277 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-144523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4660067/10000000) (δ := 19/2000000) (ψ := -272131/200000) 186 167
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t277 : ((-10856313677/625000000000 : ℚ) : ℝ) ≤ stT186 277 := by
  have hc : ((-36137/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10856313677/625000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-36137/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c278 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((368169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2984393/10000000) (δ := 19/2000000) (ψ := -272131/200000) 186 167
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t278 : ((2759788143/125000000000 : ℚ) : ℝ) ≤ stT186 278 := by
  have hc : ((368119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2759788143/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((368119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c279 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((86487/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -328691/2500000) (δ := 19/2000000) (ψ := -272131/200000) 186 167
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t279 : ((6471923711/125000000000 : ℚ) : ℝ) ≤ stT186 279 := by
  have hc : ((43241/50000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6471923711/125000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((43241/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c280 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((495137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348959/10000000) (δ := 9303/1000000000) (ψ := -272131/200000) 186 167
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t280 : ((18492866423/312500000000 : ℚ) : ℝ) ≤ stT186 280 := by
  have hc : ((61889/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18492866423/312500000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((61889/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c281 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((347393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 501671/2500000) (δ := 9303/1000000000) (ψ := -272131/200000) 186 167
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t281 : ((25902754129/625000000000 : ℚ) : ℝ) ≤ stT186 281 := by
  have hc : ((43421/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25902754129/625000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((43421/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c282 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((10717/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73171/200000) (δ := 9303/1000000000) (ψ := -272131/200000) 186 167
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t282 : ((797362449/125000000000 : ℚ) : ℝ) ≤ stT186 282 := by
  have hc : ((1339/12500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((797362449/125000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((1339/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c283 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-261781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5304557/10000000) (δ := 9303/1000000000) (ψ := -272131/200000) 186 167
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t283 : ((-77813848417/2500000000000 : ℚ) : ℝ) ≤ stT186 283 := by
  have hc : ((-130903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77813848417/2500000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-130903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c284 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-233649/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3472399/5000000) (δ := 9303/1000000000) (ψ := -272131/200000) 186 167
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t284 : ((-277305262293/5000000000000 : ℚ) : ℝ) ≤ stT186 284 := by
  have hc : ((-467323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277305262293/5000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-467323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c285 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-119777/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7128737/10000000) (δ := 1879/200000000) (ψ := -272131/200000) 186 168
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t285 : ((-283813953417/5000000000000 : ℚ) : ℝ) ≤ stT186 285 := by
  have hc : ((-479133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283813953417/5000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-479133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c286 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-117699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5499981/10000000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t286 : ((-69602861917/2000000000000 : ℚ) : ℝ) ≤ stT186 286 := by
  have hc : ((-117709/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69602861917/2000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-117709/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c287 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((20017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775389/2000000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t287 : ((11786140727/10000000000000 : ℚ) : ℝ) ≤ stT186 287 := by
  have hc : ((19967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11786140727/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((19967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c288 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((618603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1129791/5000000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t288 : ((72897089603/2000000000000 : ℚ) : ℝ) ≤ stT186 288 := by
  have hc : ((618553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72897089603/2000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((618553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c289 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((120827/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647799/10000000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t289 : ((56856795101/1000000000000 : ℚ) : ℝ) ≤ stT186 289 := by
  have hc : ((483283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56856795101/1000000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((483283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c290 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((463703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19169/200000) (δ := 1879/200000000) (ψ := -272131/200000) 186 168
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t290 : ((6807024879/125000000000 : ℚ) : ℝ) ≤ stT186 290 := by
  have hc : ((231839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6807024879/125000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((231839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c291 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((260127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31989/125000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t291 : ((7623719671/250000000000 : ℚ) : ℝ) ≤ stT186 291 := by
  have hc : ((130051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7623719671/250000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((130051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c292 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-45409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4154349/10000000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t292 : ((-6647062351/1250000000000 : ℚ) : ℝ) ≤ stT186 292 := by
  have hc : ((-22717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6647062351/1250000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-22717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c293 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-10383/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5744091/10000000) (δ := 147/15625000) (ψ := -272131/200000) 186 168
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t293 : ((-194120886167/5000000000000 : ℚ) : ℝ) ≤ stT186 293 := by
  have hc : ((-332281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194120886167/5000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-332281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c294 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-488991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 916049/1250000) (δ := 1879/200000000) (ψ := -272131/200000) 186 168
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t294 : ((-8912499981/156250000000 : ℚ) : ℝ) ≤ stT186 294 := by
  have hc : ((-61127/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8912499981/156250000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-61127/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c295 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-912539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6800617/10000000) (δ := 1863/200000000) (ψ := -272131/200000) 186 169
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t295 : ((-531330305347/10000000000000 : ℚ) : ℝ) ≤ stT186 295 := by
  have hc : ((-912589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531330305347/10000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-912589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c296 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-496887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5227011/10000000) (δ := 593/62500000) (ψ := -272131/200000) 186 169
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t296 : ((-288839164943/10000000000000 : ℚ) : ℝ) ≤ stT186 296 := by
  have hc : ((-496937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288839164943/10000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-496937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c297 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((26777/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -731741/2000000) (δ := 1863/200000000) (ψ := -272131/200000) 186 169
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t297 : ((15530315241/2500000000000 : ℚ) : ℝ) ≤ stT186 297 := by
  have hc : ((53529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15530315241/2500000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((53529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c298 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((334371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2095701/10000000) (δ := 593/62500000) (ψ := -272131/200000) 186 169
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t298 : ((24210161033/625000000000 : ℚ) : ℝ) ≤ stT186 298 := by
  have hc : ((167173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24210161033/625000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((167173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c299 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((488471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33619/625000) (δ := 1863/200000000) (ψ := -272131/200000) 186 169
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t299 : ((70618790011/1250000000000 : ℚ) : ℝ) ≤ stT186 299 := by
  have hc : ((244223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70618790011/1250000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((244223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c300 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((459379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253671/2500000) (δ := 593/62500000) (ψ := -272131/200000) 186 169
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t300 : ((2652080319/50000000000 : ℚ) : ℝ) ≤ stT186 300 := by
  have hc : ((229677/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2652080319/50000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((229677/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c301 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((8113/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2562111/10000000) (δ := 593/62500000) (ψ := -272131/200000) 186 169
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t301 : ((14962565649/500000000000 : ℚ) : ℝ) ≤ stT186 301 := by
  have hc : ((259591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14962565649/500000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((259591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c302 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-70913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4104423/10000000) (δ := 593/62500000) (ψ := -272131/200000) 186 169
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t302 : ((-10208666217/2500000000000 : ℚ) : ℝ) ≤ stT186 302 := by
  have hc : ((-70963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10208666217/2500000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-70963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c303 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-158333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 282081/500000) (δ := 593/62500000) (ψ := -272131/200000) 186 169
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t303 : ((-36386845827/1000000000000 : ℚ) : ℝ) ≤ stT186 303 := by
  have hc : ((-316691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36386845827/1000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-316691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c304 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-963211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7173749/10000000) (δ := 1863/200000000) (ψ := -272131/200000) 186 169
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t304 : ((-27623435697/500000000000 : ℚ) : ℝ) ≤ stT186 304 := by
  have hc : ((-963261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27623435697/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-963261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c305 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-943177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3503577/5000000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t305 : ((-540090836973/10000000000000 : ℚ) : ℝ) ≤ stT186 305 := by
  have hc : ((-943227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-540090836973/10000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-943227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c306 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-583647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5485023/10000000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t306 : ((-166838697207/5000000000000 : ℚ) : ℝ) ≤ stT186 306 := by
  have hc : ((-583697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166838697207/5000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-583697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c307 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-16369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1983957/5000000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t307 : ((-9370832289/10000000000000 : ℚ) : ℝ) ≤ stT186 307 := by
  have hc : ((-16419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9370832289/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-16419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c308 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((138779/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1227867/5000000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t308 : ((79069429233/2500000000000 : ℚ) : ℝ) ≤ stT186 308 := by
  have hc : ((277533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79069429233/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((277533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c309 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((14514/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -948437/10000000) (δ := 9381/1000000000) (ψ := -272131/200000) 186 170
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t309 : ((3302511953/62500000000 : ℚ) : ℝ) ≤ stT186 309 := by
  have hc : ((464423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3302511953/62500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((464423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c310 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((975549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 276989/5000000) (δ := 9381/1000000000) (ψ := -272131/200000) 186 170
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t310 : ((554045387539/10000000000000 : ℚ) : ℝ) ≤ stT186 310 := by
  have hc : ((975499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((554045387539/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((975499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c311 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((85219/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 512901/2500000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t311 : ((193278536997/5000000000000 : ℚ) : ℝ) ≤ stT186 311 := by
  have hc : ((340851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193278536997/5000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((340851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c312 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((152461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3544347/10000000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t312 : ((43142829359/5000000000000 : ℚ) : ℝ) ≤ stT186 312 := by
  have hc : ((152411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43142829359/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((152411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c313 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-427877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5032347/10000000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t313 : ((-120939444959/5000000000000 : ℚ) : ℝ) ≤ stT186 313 := by
  have hc : ((-427927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120939444959/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-427927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c314 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-86009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628901/2500000) (δ := 4711/500000000) (ψ := -272131/200000) 186 170
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t314 : ((-24270269331/500000000000 : ℚ) : ℝ) ≤ stT186 314 := by
  have hc : ((-43007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24270269331/500000000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-43007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c315 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-249607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7713799/10000000) (δ := 9329/1000000000) (ψ := -272131/200000) 186 171
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t315 : ((-281289724443/5000000000000 : ℚ) : ℝ) ≤ stT186 315 := by
  have hc : ((-499239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281289724443/5000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-499239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c316 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-99841/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1247987/2000000) (δ := 9329/1000000000) (ψ := -272131/200000) 186 171
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t316 : ((-14042117851/312500000000 : ℚ) : ℝ) ≤ stT186 316 := by
  have hc : ((-399389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14042117851/312500000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-399389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c317 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-331139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298173/625000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t317 : ((-23251786123/1250000000000 : ℚ) : ℝ) ≤ stT186 317 := by
  have hc : ((-331189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23251786123/1250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-331189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c318 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((245771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826551/2500000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t318 : ((34448364153/2500000000000 : ℚ) : ℝ) ≤ stT186 318 := by
  have hc : ((245721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34448364153/2500000000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((245721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c319 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((739493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1846197/10000000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t319 : ((103502055039/2500000000000 : ℚ) : ℝ) ≤ stT186 319 := by
  have hc : ((739443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103502055039/2500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((739443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c320 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((246951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9771/250000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t320 : ((34510643129/625000000000 : ℚ) : ℝ) ≤ stT186 320 := by
  have hc : ((493877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34510643129/625000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((493877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c321 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((455721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060053/10000000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t321 : ((3179305549/62500000000 : ℚ) : ℝ) ≤ stT186 321 := by
  have hc : ((28481/31250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3179305549/62500000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((28481/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c322 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((10763/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2506389/10000000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t322 : ((1499356459/50000000000 : ℚ) : ℝ) ≤ stT186 322 := by
  have hc : ((5381/10000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1499356459/50000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((5381/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c323 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-2127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3948261/10000000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t323 : ((-476179957/1000000000000 : ℚ) : ℝ) ≤ stT186 323 := by
  have hc : ((-4279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476179957/1000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-4279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c324 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-137731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5385669/10000000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t324 : ((-38262113943/1250000000000 : ℚ) : ℝ) ≤ stT186 324 := by
  have hc : ((-275487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38262113943/1250000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-275487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c325 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-45773/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6818613/10000000) (δ := 4737/500000000) (ψ := -272131/200000) 186 171
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t325 : ((-50783431251/1000000000000 : ℚ) : ℝ) ≤ stT186 325 := by
  have hc : ((-91551/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50783431251/1000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-91551/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c326 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-987657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7460777/10000000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t326 : ((-547040534243/10000000000000 : ℚ) : ℝ) ≤ stT186 326 := by
  have hc : ((-987707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547040534243/10000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-987707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c327 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-186799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241463/400000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t327 : ((-103307133123/2500000000000 : ℚ) : ℝ) ≤ stT186 327 := by
  have hc : ((-373623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103307133123/2500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-373623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c328 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-68099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4616697/10000000) (δ := 2359/250000000) (ψ := -272131/200000) 186 172
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t328 : ((-37608309617/2500000000000 : ℚ) : ℝ) ≤ stT186 328 := by
  have hc : ((-136223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37608309617/2500000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-136223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c329 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((286259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3201191/10000000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t329 : ((157791887253/10000000000000 : ℚ) : ℝ) ≤ stT186 329 := by
  have hc : ((286209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157791887253/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((286209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c330 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((754447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -894981/5000000) (δ := 2359/250000000) (ψ := -272131/200000) 186 172
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t330 : ((415281214957/10000000000000 : ℚ) : ℝ) ≤ stT186 330 := by
  have hc : ((754397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415281214957/10000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((754397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c331 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((988287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95753/2500000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t331 : ((543183478813/10000000000000 : ℚ) : ℝ) ≤ stT186 331 := by
  have hc : ((988237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543183478813/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((988237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c332 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((917963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1019707/10000000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t332 : ((503769930573/10000000000000 : ℚ) : ℝ) ≤ stT186 332 := by
  have hc : ((917913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((503769930573/10000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((917913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c333 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((567543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 483639/2000000) (δ := 2359/250000000) (ψ := -272131/200000) 186 172
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t333 : ((77745973507/2500000000000 : ℚ) : ℝ) ≤ stT186 333 := by
  have hc : ((567493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77745973507/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((567493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c334 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((22891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3812497/10000000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t334 : ((250234071/100000000000 : ℚ) : ℝ) ≤ stT186 334 := by
  have hc : ((11433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250234071/100000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((11433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c335 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-488411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5202661/10000000) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t335 : ((-266875063499/10000000000000 : ℚ) : ℝ) ≤ stT186 335 := by
  have hc : ((-488461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266875063499/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-488461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c336 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-13666/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41179/62500) (δ := 9367/1000000000) (ψ := -272131/200000) 186 172
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t336 : ((-47717402733/1000000000000 : ℚ) : ℝ) ≤ stT186 336 := by
  have hc : ((-437337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47717402733/1000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-437337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c337 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-499457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1934359/2500000) (δ := 73/7812500) (ψ := -272131/200000) 186 173
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t337 : ((-27208532727/500000000000 : ℚ) : ℝ) ≤ stT186 337 := by
  have hc : ((-249741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27208532727/500000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-249741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c338 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-413311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794961/1250000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t338 : ((-28103179643/625000000000 : ℚ) : ℝ) ≤ stT186 338 := by
  have hc : ((-51667/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28103179643/625000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-51667/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c339 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-205513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2492969/5000000) (δ := 73/7812500) (ψ := -272131/200000) 186 173
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t339 : ((-27908257947/1250000000000 : ℚ) : ℝ) ≤ stT186 339 := by
  have hc : ((-102769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27908257947/1250000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-102769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c340 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((30991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3616281/10000000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t340 : ((16800445991/2500000000000 : ℚ) : ℝ) ≤ stT186 340 := by
  have hc : ((61957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16800445991/2500000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((61957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c341 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((3107/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2250669/10000000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t341 : ((672959331/20000000000 : ℚ) : ℝ) ≤ stT186 341 := by
  have hc : ((12427/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((672959331/20000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((12427/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c342 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((937437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -889009/10000000) (δ := 73/7812500) (ψ := -272131/200000) 186 173
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t342 : ((253440385803/5000000000000 : ℚ) : ℝ) ≤ stT186 342 := by
  have hc : ((937387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253440385803/5000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((937387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c343 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((982481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 468651/10000000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t343 : ((530462636019/10000000000000 : ℚ) : ℝ) ≤ stT186 343 := by
  have hc : ((982431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530462636019/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((982431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c344 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((372939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1822359/10000000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t344 : ((100530715491/2500000000000 : ℚ) : ℝ) ≤ stT186 344 := by
  have hc : ((186457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100530715491/2500000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((186457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c345 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((59473/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3172161/10000000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t345 : ((32013749403/2000000000000 : ℚ) : ℝ) ≤ stT186 345 := by
  have hc : ((59463/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32013749403/2000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((59463/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c346 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-58553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4518011/10000000) (δ := 73/7812500) (ψ := -272131/200000) 186 173
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t346 : ((-15742523531/1250000000000 : ℚ) : ℝ) ≤ stT186 346 := by
  have hc : ((-117131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15742523531/1250000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-117131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c347 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-10913/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5860001/10000000) (δ := 73/7812500) (ψ := -272131/200000) 186 173
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t347 : ((-187482696789/5000000000000 : ℚ) : ℝ) ≤ stT186 347 := by
  have hc : ((-349241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187482696789/5000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-349241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c348 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-482893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7198131/10000000) (δ := 9459/1000000000) (ψ := -272131/200000) 186 173
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t348 : ((-129435787163/2500000000000 : ℚ) : ℝ) ≤ stT186 348 := by
  have hc : ((-241459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129435787163/2500000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-241459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c349 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-4817/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3587757/5000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t349 : ((-1289308059/25000000000 : ℚ) : ℝ) ≤ stT186 349 := by
  have hc : ((-19269/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1289308059/25000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-19269/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c350 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-694141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91329/156250) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t350 : ((-371061055893/10000000000000 : ℚ) : ℝ) ≤ stT186 350 := by
  have hc : ((-694191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371061055893/10000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-694191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c351 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-4687/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -903673/2000000) (δ := 1169/125000000) (ψ := -272131/200000) 186 174
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t351 : ((-156391973/12500000000 : ℚ) : ℝ) ≤ stT186 351 := by
  have hc : ((-293/1250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156391973/12500000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-293/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c352 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((57689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1597743/5000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t352 : ((30742964679/2000000000000 : ℚ) : ℝ) ≤ stT186 352 := by
  have hc : ((57679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30742964679/2000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((57679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c353 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((731327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234541/1250000) (δ := 1169/125000000) (ψ := -272131/200000) 186 174
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t353 : ((194609629071/5000000000000 : ℚ) : ℝ) ≤ stT186 353 := by
  have hc : ((731277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194609629071/5000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((731277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c354 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((487469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -560889/10000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t354 : ((32384195167/625000000000 : ℚ) : ℝ) ≤ stT186 354 := by
  have hc : ((121861/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32384195167/625000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((121861/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c355 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((238811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 750783/10000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t355 : ((31685217771/625000000000 : ℚ) : ℝ) ≤ stT186 355 := by
  have hc : ((477597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31685217771/625000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((477597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c356 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((135927/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 514707/2500000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t356 : ((36017869083/1000000000000 : ℚ) : ℝ) ≤ stT186 356 := by
  have hc : ((135917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36017869083/1000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((135917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c357 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((55907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3363153/10000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t357 : ((7395624873/625000000000 : ℚ) : ℝ) ≤ stT186 357 := by
  have hc : ((111789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7395624873/625000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((111789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c358 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-58099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4663851/10000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t358 : ((-30711594353/2000000000000 : ℚ) : ℝ) ≤ stT186 358 := by
  have hc : ((-58109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30711594353/2000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-58109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c359 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-363373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2980461/5000000) (δ := 9451/1000000000) (ψ := -272131/200000) 186 174
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t359 : ((-4794854911/125000000000 : ℚ) : ℝ) ≤ stT186 359 := by
  have hc : ((-181699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4794854911/125000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-181699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c360 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-971379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1813603/2500000) (δ := 1169/125000000) (ψ := -272131/200000) 186 174
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t360 : ((-511988740163/10000000000000 : ℚ) : ℝ) ≤ stT186 360 := by
  have hc : ((-971429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-511988740163/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-971429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c361 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-962121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895461/1250000) (δ := 1889/200000000) (ψ := -272131/200000) 186 175
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t361 : ((-126601498009/2500000000000 : ℚ) : ℝ) ≤ stT186 361 := by
  have hc : ((-962171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126601498009/2500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-962171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c362 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-87923/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2938679/5000000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t362 : ((-184858586313/5000000000000 : ℚ) : ℝ) ≤ stT186 362 := by
  have hc : ((-351717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184858586313/5000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-351717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c363 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-52777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4594609/10000000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t363 : ((-432906187/31250000000 : ℚ) : ℝ) ≤ stT186 363 := by
  have hc : ((-52787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432906187/31250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-52787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c364 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((121103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1657697/5000000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t364 : ((15865516269/1250000000000 : ℚ) : ℝ) ≤ stT186 364 := by
  have hc : ((60539/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15865516269/1250000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((60539/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c365 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((685237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2039667/10000000) (δ := 1889/200000000) (ψ := -272131/200000) 186 175
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t365 : ((358642635101/10000000000000 : ℚ) : ℝ) ≤ stT186 365 := by
  have hc : ((685187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358642635101/10000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((685187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c366 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((953253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -767427/10000000) (δ := 1889/200000000) (ψ := -272131/200000) 186 175
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t366 : ((124561708431/2500000000000 : ℚ) : ℝ) ≤ stT186 366 := by
  have hc : ((953203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124561708431/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((953203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c367 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((979961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250663/5000000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t367 : ((102301728489/2000000000000 : ℚ) : ℝ) ≤ stT186 367 := by
  have hc : ((979911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102301728489/2000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((979911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c368 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((380269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1766637/10000000) (δ := 1889/200000000) (ψ := -272131/200000) 186 175
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t368 : ((24776984223/625000000000 : ℚ) : ℝ) ≤ stT186 368 := by
  have hc : ((95061/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24776984223/625000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((95061/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c369 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((175853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757127/2500000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t369 : ((22883091103/1250000000000 : ℚ) : ℝ) ≤ stT186 369 := by
  have hc : ((43957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22883091103/1250000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((43957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c370 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-287/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535873/1250000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t370 : ((-373140999/50000000000 : ℚ) : ℝ) ≤ stT186 370 := by
  have hc : ((-2871/20000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373140999/50000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-2871/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c371 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-301003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5542019/10000000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t371 : ((-1562862119/50000000000 : ℚ) : ℝ) ≤ stT186 371 := by
  have hc : ((-75257/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1562862119/50000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-75257/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c372 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-182281/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3396853/5000000) (δ := 4679/500000000) (ψ := -272131/200000) 186 175
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t372 : ((-23628377129/500000000000 : ℚ) : ℝ) ≤ stT186 372 := by
  have hc : ((-182291/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23628377129/500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-182291/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c373 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-249293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3832959/5000000) (δ := 1893/200000000) (ψ := -272131/200000) 186 176
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t373 : ((-258171302191/5000000000000 : ℚ) : ℝ) ≤ stT186 373 := by
  have hc : ((-498611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258171302191/5000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-498611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c374 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-105021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3210487/5000000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t374 : ((-6788541331/156250000000 : ℚ) : ℝ) ≤ stT186 374 := by
  have hc : ((-420109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6788541331/156250000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-420109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c375 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-48023/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1294821/2500000) (δ := 1893/200000000) (ψ := -272131/200000) 186 176
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t375 : ((-3100195393/125000000000 : ℚ) : ℝ) ≤ stT186 375 := by
  have hc : ((-12007/25000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3100195393/125000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-12007/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c376 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-5581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3940943/10000000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t376 : ((-2903968641/10000000000000 : ℚ) : ℝ) ≤ stT186 376 := by
  have hc : ((-5631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2903968641/10000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-5631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c377 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((93849/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2705903/10000000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t377 : ((24164762407/1000000000000 : ℚ) : ℝ) ≤ stT186 377 := by
  have hc : ((93839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24164762407/1000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((93839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c378 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((831137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -737059/5000000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t378 : ((53433076491/1250000000000 : ℚ) : ℝ) ≤ stT186 378 := by
  have hc : ((831087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53433076491/1250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((831087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c379 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((995181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245541/10000000) (δ := 1893/200000000) (ψ := -272131/200000) 186 176
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t379 : ((102232793023/2000000000000 : ℚ) : ℝ) ≤ stT186 379 := by
  have hc : ((995131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102232793023/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((995131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c380 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((924187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489867/5000000) (δ := 1893/200000000) (ψ := -272131/200000) 186 176
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t380 : ((474072115493/10000000000000 : ℚ) : ℝ) ≤ stT186 380 := by
  have hc : ((924137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474072115493/10000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((924137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c381 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((159149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11009/50000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t381 : ((32611206399/1000000000000 : ℚ) : ℝ) ≤ stT186 381 := by
  have hc : ((318273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32611206399/1000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((318273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c382 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((201133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 684141/2000000) (δ := 1893/200000000) (ψ := -272131/200000) 186 176
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t382 : ((25720727613/2500000000000 : ℚ) : ℝ) ≤ stT186 382 := by
  have hc : ((201083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25720727613/2500000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((201083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c383 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-279953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2318177/5000000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t383 : ((-143075092931/10000000000000 : ℚ) : ℝ) ≤ stT186 383 := by
  have hc : ((-280003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143075092931/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-280003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c384 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-173811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731111/1250000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t384 : ((-177408088217/5000000000000 : ℚ) : ℝ) ≤ stT186 384 := by
  have hc : ((-347647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177408088217/5000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-347647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c385 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-237443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352913/500000) (δ := 4669/500000000) (ψ := -272131/200000) 186 176
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t385 : ((-15127340083/312500000000 : ℚ) : ℝ) ≤ stT186 385 := by
  have hc : ((-474911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15127340083/312500000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-474911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c386 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-19731/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7443493/10000000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t386 : ((-2510832871/50000000000 : ℚ) : ℝ) ≤ stT186 386 := by
  have hc : ((-4933/5000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2510832871/50000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-4933/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c387 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-798839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6240399/10000000) (δ := 9431/1000000000) (ψ := -272131/200000) 186 177
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t387 : ((-406098446481/10000000000000 : ℚ) : ℝ) ≤ stT186 387 := by
  have hc : ((-798889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406098446481/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-798889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c388 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-53847/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5040373/10000000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t388 : ((-54679789681/2500000000000 : ℚ) : ℝ) ≤ stT186 388 := by
  have hc : ((-215413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54679789681/2500000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-215413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c389 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((6681/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3843463/10000000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t389 : ((169116521/100000000000 : ℚ) : ℝ) ≤ stT186 389 := by
  have hc : ((6671/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169116521/100000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((6671/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c390 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((122251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1324811/5000000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t390 : ((123795574013/5000000000000 : ℚ) : ℝ) ≤ stT186 390 := by
  have hc : ((244477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123795574013/5000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((244477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c391 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((834517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29177/200000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t391 : ((422007485707/10000000000000 : ℚ) : ℝ) ≤ stT186 391 := by
  have hc : ((834467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422007485707/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((834467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c392 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((497063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -271101/10000000) (δ := 9431/1000000000) (ψ := -272131/200000) 186 177
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t392 : ((31380245611/625000000000 : ℚ) : ℝ) ≤ stT186 392 := by
  have hc : ((248519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31380245611/625000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((248519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c393 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((933963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 456813/5000000) (δ := 9431/1000000000) (ψ := -272131/200000) 186 177
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t393 : ((471096536329/10000000000000 : ℚ) : ℝ) ≤ stT186 393 := by
  have hc : ((933913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471096536329/10000000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((933913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c394 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((167213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2095331/10000000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t394 : ((10529284287/312500000000 : ℚ) : ℝ) ≤ stT186 394 := by
  have hc : ((334401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10529284287/312500000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((334401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c395 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((258231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3274013/10000000) (δ := 2343/250000000) (ψ := -272131/200000) 186 177
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t395 : ((64952401437/5000000000000 : ℚ) : ℝ) ≤ stT186 395 := by
  have hc : ((258181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64952401437/5000000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((258181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c396 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-207589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889953/2000000) (δ := 9431/1000000000) (ψ := -272131/200000) 186 177
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t396 : ((-104342542641/10000000000000 : ℚ) : ℝ) ≤ stT186 396 := by
  have hc : ((-207639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104342542641/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-207639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c397 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-313697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1124499/2000000) (δ := 9431/1000000000) (ψ := -272131/200000) 186 177
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t397 : ((-39363169923/1250000000000 : ℚ) : ℝ) ≤ stT186 397 := by
  have hc : ((-156861/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39363169923/1250000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-156861/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c398 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-911181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3396171/5000000) (δ := 9431/1000000000) (ψ := -272131/200000) 186 177
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t398 : ((-91351818981/2000000000000 : ℚ) : ℝ) ≤ stT186 398 := by
  have hc : ((-911231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91351818981/2000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-911231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c399 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-499557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6199/8000) (δ := 2331/250000000) (ψ := -272131/200000) 186 178
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t399 : ((-125052118957/2500000000000 : ℚ) : ℝ) ≤ stT186 399 := by
  have hc : ((-249791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125052118957/2500000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-249791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c400 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-21847/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -823101/1250000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t400 : ((-43696587393/1000000000000 : ℚ) : ℝ) ≤ stT186 400 := by
  have hc : ((-87393/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43696587393/1000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-87393/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c401 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-140893/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4339/8000) (δ := 2331/250000000) (ψ := -272131/200000) 186 178
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t401 : ((-140729931747/5000000000000 : ℚ) : ℝ) ≤ stT186 401 := by
  have hc : ((-281811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140729931747/5000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-281811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c402 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-67519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4265621/10000000) (δ := 2331/250000000) (ψ := -272131/200000) 186 178
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t402 : ((-842197693/125000000000 : ℚ) : ℝ) ≤ stT186 402 := by
  have hc : ((-8443/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-842197693/125000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-8443/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c403 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((160443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388791/1250000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t403 : ((7990982043/500000000000 : ℚ) : ℝ) ≤ stT186 403 := by
  have hc : ((80209/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7990982043/500000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((80209/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c404 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((354341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957919/10000000) (δ := 2331/250000000) (ψ := -272131/200000) 186 178
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t404 : ((22034823461/625000000000 : ℚ) : ℝ) ≤ stT186 404 := by
  have hc : ((88579/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22034823461/625000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((88579/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c405 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((47409/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404173/5000000) (δ := 2331/250000000) (ψ := -272131/200000) 186 178
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t405 : ((47112864139/1000000000000 : ℚ) : ℝ) ≤ stT186 405 := by
  have hc : ((94813/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47112864139/1000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((94813/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c406 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((990853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 338391/10000000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t406 : ((491726611673/10000000000000 : ℚ) : ℝ) ≤ stT186 406 := by
  have hc : ((990803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((491726611673/10000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((990803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c407 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((165863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1482291/10000000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t407 : ((82210180893/2000000000000 : ℚ) : ℝ) ≤ stT186 407 := by
  have hc : ((165853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82210180893/2000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((165853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c408 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((249063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2623401/10000000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t408 : ((61645994887/2500000000000 : ℚ) : ℝ) ≤ stT186 408 := by
  have hc : ((124519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61645994887/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((124519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c409 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((3303/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3761721/10000000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t409 : ((815995817/250000000000 : ℚ) : ℝ) ≤ stT186 409 := by
  have hc : ((6601/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((815995817/250000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((6601/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c410 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-189217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4897251/10000000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t410 : ((-9346000033/500000000000 : ℚ) : ℝ) ≤ stT186 410 := by
  have hc : ((-94621/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9346000033/500000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-94621/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c411 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-46591/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6030037/10000000) (δ := 2331/250000000) (ψ := -272131/200000) 186 178
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t411 : ((-11491602237/312500000000 : ℚ) : ℝ) ≤ stT186 411 := by
  have hc : ((-372753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11491602237/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-372753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c412 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-480861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3580017/5000000) (δ := 9479/1000000000) (ψ := -272131/200000) 186 178
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t412 : ((-23691570119/500000000000 : ℚ) : ℝ) ≤ stT186 412 := by
  have hc : ((-240443/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23691570119/500000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-240443/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c413 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-985017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7420677/10000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t413 : ((-121179987139/2500000000000 : ℚ) : ℝ) ≤ stT186 413 := by
  have hc : ((-985067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121179987139/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-985067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c414 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-50753/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6296121/10000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t414 : ((-99781263113/2500000000000 : ℚ) : ℝ) ≤ stT186 414 := by
  have hc : ((-406049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99781263113/2500000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-406049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c415 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-478467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2587131/5000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t415 : ((-234894903477/10000000000000 : ℚ) : ℝ) ≤ stT186 415 := by
  have hc : ((-478517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234894903477/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-478517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c416 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-1281/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2027573/5000000) (δ := 9387/1000000000) (ψ := -272131/200000) 186 179
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t416 : ((-2514702539/1000000000000 : ℚ) : ℝ) ≤ stT186 416 := by
  have hc : ((-5129/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2514702539/1000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-5129/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c417 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((385107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2938681/10000000) (δ := 9387/1000000000) (ψ := -272131/200000) 186 179
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t417 : ((94281591507/5000000000000 : ℚ) : ℝ) ≤ stT186 417 := by
  have hc : ((385057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94281591507/5000000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((385057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c418 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((372599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1824913/10000000) (δ := 9387/1000000000) (ψ := -272131/200000) 186 179
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t418 : ((18223153201/500000000000 : ℚ) : ℝ) ≤ stT186 418 := by
  have hc : ((186287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18223153201/500000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((186287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c419 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((239879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -178449/2500000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t419 : ((234364442223/5000000000000 : ℚ) : ℝ) ≤ stT186 419 := by
  have hc : ((479733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234364442223/5000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((479733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c420 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((197513/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 394671/10000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t420 : ((1927431777/40000000000 : ℚ) : ℝ) ≤ stT186 420 := by
  have hc : ((197503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1927431777/40000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((197503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c421 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((33009/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187561/1250000) (δ := 9387/1000000000) (ψ := -272131/200000) 186 179
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t421 : ((1608662159/40000000000 : ℚ) : ℝ) ≤ stT186 421 := by
  have hc : ((33007/40000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1608662159/40000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((33007/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c422 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((504943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26037/100000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t422 : ((30722234157/1250000000000 : ℚ) : ℝ) ≤ stT186 422 := by
  have hc : ((504893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30722234157/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((504893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c423 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((44487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852131/5000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t423 : ((1351133487/312500000000 : ℚ) : ℝ) ≤ stT186 423 := by
  have hc : ((22231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1351133487/312500000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((22231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c424 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-171501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4802267/10000000) (δ := 9387/1000000000) (ψ := -272131/200000) 186 179
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t424 : ((-41650200609/2500000000000 : ℚ) : ℝ) ≤ stT186 424 := by
  have hc : ((-85763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41650200609/2500000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-85763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c425 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-141827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5897667/10000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t425 : ((-4300072329/125000000000 : ℚ) : ℝ) ≤ stT186 425 := by
  have hc : ((-141837/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4300072329/125000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-141837/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c426 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-58809/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699051/1000000) (δ := 1177/125000000) (ψ := -272131/200000) 186 179
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t426 : ((-113978368747/2500000000000 : ℚ) : ℝ) ≤ stT186 426 := by
  have hc : ((-470497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113978368747/2500000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-470497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c427 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-995887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7627167/10000000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t427 : ((-240983888079/5000000000000 : ℚ) : ℝ) ≤ stT186 427 := by
  have hc : ((-995937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240983888079/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-995937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c428 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-216231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3269743/5000000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t428 : ((-209050808703/5000000000000 : ℚ) : ℝ) ≤ stT186 428 := by
  have hc : ((-432487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209050808703/5000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-432487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c429 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-286807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5454269/10000000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t429 : ((-1731049047/62500000000 : ℚ) : ℝ) ≤ stT186 429 := by
  have hc : ((-17927/31250 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1731049047/62500000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-17927/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c430 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-176911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4371609/10000000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t430 : ((-85338203523/10000000000000 : ℚ) : ℝ) ≤ stT186 430 := by
  have hc : ((-176961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85338203523/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-176961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c431 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((50293/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3291507/10000000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t431 : ((24220466289/2000000000000 : ℚ) : ℝ) ≤ stT186 431 := by
  have hc : ((50283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24220466289/2000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((50283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c432 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((126573/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221387/1000000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t432 : ((487140987/16000000000 : ℚ) : ℝ) ≤ stT186 432 := by
  have hc : ((126563/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487140987/16000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((126563/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c433 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((898051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1138697/10000000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t433 : ((431551442569/10000000000000 : ℚ) : ℝ) ≤ stT186 433 := by
  have hc : ((898001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((431551442569/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((898001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c434 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((999651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13207/2000000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t434 : ((95964694803/2000000000000 : ℚ) : ℝ) ≤ stT186 434 := by
  have hc : ((999601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95964694803/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((999601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c435 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((920411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1004163/10000000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t435 : ((441279046143/10000000000000 : ℚ) : ℝ) ≤ stT186 435 := by
  have hc : ((920361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441279046143/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((920361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c436 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((675791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258987/1250000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t436 : ((323621149533/10000000000000 : ℚ) : ℝ) ≤ stT186 436 := by
  have hc : ((675741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323621149533/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((675741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c437 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((310701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 784291/2500000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t437 : ((37151063741/2500000000000 : ℚ) : ℝ) ≤ stT186 437 := by
  have hc : ((310651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37151063741/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((310651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c438 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-109011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4200061/10000000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t438 : ((-52111417959/10000000000000 : ℚ) : ℝ) ≤ stT186 438 := by
  have hc : ((-109061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52111417959/10000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-109061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c439 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-101693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2630247/5000000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t439 : ((-24270098811/1000000000000 : ℚ) : ℝ) ≤ stT186 439 := by
  have hc : ((-101703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24270098811/1000000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-101703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c440 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-817241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1579627/2500000) (δ := 9309/1000000000) (ψ := -272131/200000) 186 180
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t440 : ((-97407193253/2500000000000 : ℚ) : ℝ) ≤ stT186 440 := by
  have hc : ((-817291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97407193253/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-817291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c441 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-490817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1474821/2000000) (δ := 4747/500000000) (ψ := -272131/200000) 186 180
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t441 : ((-116867271411/2500000000000 : ℚ) : ℝ) ≤ stT186 441 := by
  have hc : ((-245421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116867271411/2500000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-245421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c442 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-973817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3640317/5000000) (δ := 4701/500000000) (ψ := -272131/200000) 186 181
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t442 : ((-115805446571/2500000000000 : ℚ) : ℝ) ≤ stT186 442 := by
  have hc : ((-973867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115805446571/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-973867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c443 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-796277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311489/500000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t443 : ((-75669380521/2000000000000 : ℚ) : ℝ) ≤ stT186 443 := by
  have hc : ((-796327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75669380521/2000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-796327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c444 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-480937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2590649/5000000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t444 : ((-228266329473/10000000000000 : ℚ) : ℝ) ≤ stT186 444 := by
  have hc : ((-480987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228266329473/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-480987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c445 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-83183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1033797/2500000) (δ := 4701/500000000) (ψ := -272131/200000) 186 181
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t445 : ((-19728135359/5000000000000 : ℚ) : ℝ) ≤ stT186 445 := by
  have hc : ((-83233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19728135359/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-83233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c446 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((328047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1545701/5000000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t446 : ((155310843461/10000000000000 : ℚ) : ℝ) ≤ stT186 446 := by
  have hc : ((327997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155310843461/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((327997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c447 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((27289/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -512497/2500000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t447 : ((12906287121/400000000000 : ℚ) : ℝ) ≤ stT186 447 := by
  have hc : ((27287/40000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12906287121/400000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((27287/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c448 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((459681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1010853/10000000) (δ := 4701/500000000) (ψ := -272131/200000) 186 181
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t448 : ((5429169387/125000000000 : ℚ) : ℝ) ≤ stT186 448 := by
  have hc : ((57457/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5429169387/125000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((57457/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c449 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((499973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25911/10000000) (δ := 4701/500000000) (ψ := -272131/200000) 186 181
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t449 : ((58984989923/1250000000000 : ℚ) : ℝ) ≤ stT186 449 := by
  have hc : ((124987/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58984989923/1250000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((124987/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c450 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((182277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1060397/10000000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t450 : ((21480348217/500000000000 : ℚ) : ℝ) ≤ stT186 450 := by
  have hc : ((182267/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21480348217/500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((182267/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c451 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((669663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 523151/2500000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t451 : ((315308039053/10000000000000 : ℚ) : ℝ) ≤ stT186 451 := by
  have hc : ((669613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315308039053/10000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((669613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c452 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((316277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1561243/5000000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t452 : ((3718513293/250000000000 : ℚ) : ℝ) ≤ stT186 452 := by
  have hc : ((316227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3718513293/250000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((316227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c453 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-4457/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518767/1250000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t453 : ((-4190511879/1000000000000 : ℚ) : ℝ) ≤ stT186 453 := by
  have hc : ((-8919/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4190511879/1000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-8919/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c454 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-59861/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5175461/10000000) (δ := 9401/1000000000) (ψ := -272131/200000) 186 181
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t454 : ((-28097137239/1250000000000 : ℚ) : ℝ) ≤ stT186 454 := by
  have hc : ((-239469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28097137239/1250000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-239469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c455 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-788671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30993/50000) (δ := 4701/500000000) (ψ := -272131/200000) 186 181
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t455 : ((-46219839321/1250000000000 : ℚ) : ℝ) ≤ stT186 455 := by
  have hc : ((-788721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46219839321/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-788721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c456 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-967963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7219461/10000000) (δ := 4701/500000000) (ψ := -272131/200000) 186 181
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t456 : ((-453313711809/10000000000000 : ℚ) : ℝ) ≤ stT186 456 := by
  have hc : ((-968013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453313711809/10000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-968013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c457 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-988223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46687/62500) (δ := 1899/200000000) (ψ := -272131/200000) 186 182
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t457 : ((-462295332213/10000000000000 : ℚ) : ℝ) ≤ stT186 457 := by
  have hc : ((-988273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-462295332213/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-988273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c458 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-423579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6453523/10000000) (δ := 1899/200000000) (ψ := -272131/200000) 186 182
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t458 : ((-4948436027/125000000000 : ℚ) : ℝ) ≤ stT186 458 := by
  have hc : ((-105901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4948436027/125000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-105901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c459 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-568703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5439311/10000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t459 : ((-265471719033/10000000000000 : ℚ) : ℝ) ≤ stT186 459 := by
  have hc : ((-568753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265471719033/10000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-568753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c460 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-198821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2213689/5000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t460 : ((-92724200363/10000000000000 : ℚ) : ℝ) ≤ stT186 460 := by
  have hc : ((-198871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92724200363/10000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-198871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c461 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((50589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213599/625000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t461 : ((23555802569/2500000000000 : ℚ) : ℝ) ≤ stT186 461 := by
  have hc : ((101153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23555802569/2500000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((101153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c462 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((570231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1205011/5000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t462 : ((132636074401/5000000000000 : ℚ) : ℝ) ≤ stT186 462 := by
  have hc : ((570181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132636074401/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((570181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c463 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((846277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1404599/10000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t463 : ((393274689753/10000000000000 : ℚ) : ℝ) ≤ stT186 463 := by
  have hc : ((846227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((393274689753/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((846227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c464 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((49357/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200681/5000000) (δ := 1899/200000000) (ψ := -272131/200000) 186 182
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t464 : ((22912234371/500000000000 : ℚ) : ℝ) ≤ stT186 464 := by
  have hc : ((98709/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22912234371/500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((98709/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c465 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((971363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599737/10000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t465 : ((225217373997/5000000000000 : ℚ) : ℝ) ≤ stT186 465 := by
  have hc : ((971313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225217373997/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((971313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c466 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((401209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31973/200000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t466 : ((5807652417/156250000000 : ℚ) : ℝ) ≤ stT186 466 := by
  have hc : ((12537/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5807652417/156250000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((12537/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c467 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((253899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 81107/312500) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t467 : ((7342416891/312500000000 : ℚ) : ℝ) ≤ stT186 467 := by
  have hc : ((126937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7342416891/312500000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((126937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c468 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((26873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3590059/10000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t468 : ((49669687/8000000000 : ℚ) : ℝ) ≤ stT186 468 := by
  have hc : ((26863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49669687/8000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((26863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c469 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-259249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4582601/10000000) (δ := 1899/200000000) (ψ := -272131/200000) 186 182
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t469 : ((-59866693821/5000000000000 : ℚ) : ℝ) ≤ stT186 469 := by
  have hc : ((-259299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59866693821/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-259299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c470 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-611857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1114601/2000000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t470 : ((-141125947131/5000000000000 : ℚ) : ℝ) ≤ stT186 470 := by
  have hc : ((-611907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141125947131/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-611907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c471 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-869273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1640329/2500000) (δ := 2327/250000000) (ψ := -272131/200000) 186 182
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t471 : ((-50070396831/1250000000000 : ℚ) : ℝ) ≤ stT186 471 := by
  have hc : ((-869323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50070396831/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-869323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c472 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-992497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3773767/5000000) (δ := 1899/200000000) (ψ := -272131/200000) 186 182
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t472 : ((-892299753/19531250000 : ℚ) : ℝ) ≤ stT186 472 := by
  have hc : ((-992547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-892299753/19531250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-992547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c473 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-192697/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7176303/10000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t473 : ((-88606871307/2000000000000 : ℚ) : ℝ) ≤ stT186 473 := by
  have hc : ((-192707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88606871307/2000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-192707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c474 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-787593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6194223/10000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t474 : ((-90444258047/2500000000000 : ℚ) : ℝ) ≤ stT186 474 := by
  have hc : ((-787643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90444258047/2500000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-787643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c475 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-246223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1042847/2000000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t475 : ((-882706737/39062500000 : ℚ) : ℝ) ≤ stT186 475 := by
  have hc : ((-30781/62500 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-882706737/39062500000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-30781/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c476 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-3857/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211817/500000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t476 : ((-565943079/100000000000 : ℚ) : ℝ) ≤ stT186 476 := by
  have hc : ((-61737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-565943079/100000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-61737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c477 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((263453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3260491/10000000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t477 : ((30150951201/2500000000000 : ℚ) : ℝ) ≤ stT186 477 := by
  have hc : ((263403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30150951201/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((263403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c478 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((610063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1143321/5000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t478 : ((279013236057/10000000000000 : ℚ) : ℝ) ≤ stT186 478 := by
  have hc : ((610013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279013236057/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((610013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c479 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((172969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262977/2000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t479 : ((79026869649/2000000000000 : ℚ) : ℝ) ≤ stT186 479 := by
  have hc : ((172959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79026869649/2000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((172959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c480 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((990489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345081/10000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t480 : ((90414204993/2000000000000 : ℚ) : ℝ) ≤ stT186 480 := by
  have hc : ((990439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90414204993/2000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((990439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c481 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((484573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622631/10000000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t481 : ((1380840663/31250000000 : ℚ) : ℝ) ≤ stT186 481 := by
  have hc : ((121137/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1380840663/31250000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((121137/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c482 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((804861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1588389/10000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t482 : ((366580947957/10000000000000 : ℚ) : ℝ) ≤ stT186 482 := by
  have hc : ((804811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366580947957/10000000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((804811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c483 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((522649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1276051/5000000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t483 : ((47558076797/2000000000000 : ℚ) : ℝ) ≤ stT186 483 := by
  have hc : ((522599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47558076797/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((522599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c484 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((164501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3513861/10000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t484 : ((14950075959/2000000000000 : ℚ) : ℝ) ≤ stT186 484 := by
  have hc : ((164451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14950075959/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((164451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c485 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-3389/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 178943/400000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t485 : ((-49255094421/5000000000000 : ℚ) : ℝ) ≤ stT186 485 := by
  have hc : ((-108473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49255094421/5000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-108473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c486 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-566091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2715691/5000000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t486 : ((-25680721901/1000000000000 : ℚ) : ℝ) ≤ stT186 486 := by
  have hc : ((-566141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25680721901/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-566141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c487 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-832763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6387189/10000000) (δ := 2347/250000000) (ψ := -272131/200000) 186 183
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t487 : ((-47173026759/1250000000000 : ℚ) : ℝ) ≤ stT186 487 := by
  have hc : ((-832813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47173026759/1250000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-832813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c488 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-39161/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1835261/2500000) (δ := 1883/200000000) (ψ := -272131/200000) 186 183
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t488 : ((-17728267677/400000000000 : ℚ) : ℝ) ≤ stT186 488 := by
  have hc : ((-39163/40000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17728267677/400000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-39163/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c489 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-246157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483013/2000000) (δ := 237/25000000) (ψ := -272131/200000) 186 184
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t489 : ((-27830446653/625000000000 : ℚ) : ℝ) ≤ stT186 489 := by
  have hc : ((-492339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27830446653/625000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-492339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c490 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-212403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616279/2500000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t490 : ((-95959551787/2500000000000 : ℚ) : ℝ) ≤ stT186 490 := by
  have hc : ((-424831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95959551787/2500000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-424831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c491 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-594009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2758537/5000000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t491 : ((-134047631173/5000000000000 : ℚ) : ℝ) ≤ stT186 491 := by
  have hc : ((-594059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134047631173/5000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-594059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c492 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((-127379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914197/2000000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t492 : ((-2871909117/250000000000 : ℚ) : ℝ) ≤ stT186 492 := by
  have hc : ((-31851/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2871909117/250000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-31851/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c493 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((119769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3626849/10000000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t493 : ((53918684063/10000000000000 : ℚ) : ℝ) ≤ stT186 493 := by
  have hc : ((119719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53918684063/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((119719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c494 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((238381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2684573/10000000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t494 : ((26810342469/1250000000000 : ℚ) : ℝ) ≤ stT186 494 := by
  have hc : ((59589/125000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26810342469/1250000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((59589/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c495 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((383161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6977/40000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t495 : ((2690728209/78125000000 : ℚ) : ℝ) ≤ stT186 495 := by
  have hc : ((11973/15625 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2690728209/78125000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((11973/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c496 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((189701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -805787/10000000) (δ := 9323/1000000000) (ψ := -272131/200000) 186 184
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t496 : ((85173724983/2000000000000 : ℚ) : ℝ) ≤ stT186 496 := by
  have hc : ((189691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85173724983/2000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((189691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c497 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((124829/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130769/10000000) (δ := 237/25000000) (ψ := -272131/200000) 186 184
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t497 : ((223962470251/5000000000000 : ℚ) : ℝ) ≤ stT186 497 := by
  have hc : ((499291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223962470251/5000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((499291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c498 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((910557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1065419/10000000) (δ := 237/25000000) (ψ := -272131/200000) 186 184
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t498 : ((40800729177/1000000000000 : ℚ) : ℝ) ≤ stT186 498 := by
  have hc : ((910507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40800729177/1000000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((910507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c499 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((34861/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1998209/10000000) (δ := 237/25000000) (ψ := -272131/200000) 186 184
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t499 : ((31209581937/1000000000000 : ℚ) : ℝ) ≤ stT186 499 := by
  have hc : ((69717/100000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31209581937/1000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((69717/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_c500 :
    |Real.cos (((186 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((388627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2929139/10000000) (δ := 237/25000000) (ψ := -272131/200000) 186 184
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st186_t500 : ((173776685901/10000000000000 : ℚ) : ℝ) ≤ stT186 500 := by
  have hc : ((388577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((186 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st186_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173776685901/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((388577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st186_p1 : ((52137/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT186 (i+1) := by
  rw [Finset.sum_range_one]
  exact st186_t1

theorem st186_p2 : ((181137252767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT186 (i+1))
      = (∑ i ∈ Finset.range 1, stT186 (i+1)) + stT186 2 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 1
    simpa using h
  have hprev := st186_p1
  have hstep := st186_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p3 : ((517355308907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT186 (i+1))
      = (∑ i ∈ Finset.range 2, stT186 (i+1)) + stT186 3 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 2
    simpa using h
  have hprev := st186_p2
  have hstep := st186_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p4 : ((442215293879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT186 (i+1))
      = (∑ i ∈ Finset.range 3, stT186 (i+1)) + stT186 4 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 3
    simpa using h
  have hprev := st186_p3
  have hstep := st186_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p5 : ((3744714218923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT186 (i+1))
      = (∑ i ∈ Finset.range 4, stT186 (i+1)) + stT186 5 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 4
    simpa using h
  have hprev := st186_p4
  have hstep := st186_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p6 : ((1773710031491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT186 (i+1))
      = (∑ i ∈ Finset.range 5, stT186 (i+1)) + stT186 6 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 5
    simpa using h
  have hprev := st186_p5
  have hstep := st186_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p7 : ((2588795929557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT186 (i+1))
      = (∑ i ∈ Finset.range 6, stT186 (i+1)) + stT186 7 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 6
    simpa using h
  have hprev := st186_p6
  have hstep := st186_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p8 : ((713259532611/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT186 (i+1))
      = (∑ i ∈ Finset.range 7, stT186 (i+1)) + stT186 8 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 7
    simpa using h
  have hprev := st186_p7
  have hstep := st186_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p9 : ((2742069774917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT186 (i+1))
      = (∑ i ∈ Finset.range 8, stT186 (i+1)) + stT186 9 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 8
    simpa using h
  have hprev := st186_p8
  have hstep := st186_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p10 : ((1592357200179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT186 (i+1))
      = (∑ i ∈ Finset.range 9, stT186 (i+1)) + stT186 10 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 9
    simpa using h
  have hprev := st186_p9
  have hstep := st186_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p11 : ((4097977052493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT186 (i+1))
      = (∑ i ∈ Finset.range 10, stT186 (i+1)) + stT186 11 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 10
    simpa using h
  have hprev := st186_p10
  have hstep := st186_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p12 : ((2290798667137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT186 (i+1))
      = (∑ i ∈ Finset.range 11, stT186 (i+1)) + stT186 12 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 11
    simpa using h
  have hprev := st186_p11
  have hstep := st186_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p13 : ((3131787657637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT186 (i+1))
      = (∑ i ∈ Finset.range 12, stT186 (i+1)) + stT186 13 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 12
    simpa using h
  have hprev := st186_p12
  have hstep := st186_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p14 : ((4830063207851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT186 (i+1))
      = (∑ i ∈ Finset.range 13, stT186 (i+1)) + stT186 14 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 13
    simpa using h
  have hprev := st186_p13
  have hstep := st186_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p15 : ((2920460291297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT186 (i+1))
      = (∑ i ∈ Finset.range 14, stT186 (i+1)) + stT186 15 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 14
    simpa using h
  have hprev := st186_p14
  have hstep := st186_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p16 : ((2253095024351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT186 (i+1))
      = (∑ i ∈ Finset.range 15, stT186 (i+1)) + stT186 16 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 15
    simpa using h
  have hprev := st186_p15
  have hstep := st186_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p17 : ((4319670536627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT186 (i+1))
      = (∑ i ∈ Finset.range 16, stT186 (i+1)) + stT186 17 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 16
    simpa using h
  have hprev := st186_p16
  have hstep := st186_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p18 : ((4756964114243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT186 (i+1))
      = (∑ i ∈ Finset.range 17, stT186 (i+1)) + stT186 18 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 17
    simpa using h
  have hprev := st186_p17
  have hstep := st186_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p19 : ((616404001173/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT186 (i+1))
      = (∑ i ∈ Finset.range 18, stT186 (i+1)) + stT186 19 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 18
    simpa using h
  have hprev := st186_p18
  have hstep := st186_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p20 : ((1219981860287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT186 (i+1))
      = (∑ i ∈ Finset.range 19, stT186 (i+1)) + stT186 20 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 19
    simpa using h
  have hprev := st186_p19
  have hstep := st186_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p21 : ((3675990918521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT186 (i+1))
      = (∑ i ∈ Finset.range 20, stT186 (i+1)) + stT186 21 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 20
    simpa using h
  have hprev := st186_p20
  have hstep := st186_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p22 : ((3278049493313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT186 (i+1))
      = (∑ i ∈ Finset.range 21, stT186 (i+1)) + stT186 22 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 21
    simpa using h
  have hprev := st186_p21
  have hstep := st186_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p23 : ((5309901382961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT186 (i+1))
      = (∑ i ∈ Finset.range 22, stT186 (i+1)) + stT186 23 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 22
    simpa using h
  have hprev := st186_p22
  have hstep := st186_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p24 : ((4729123126637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT186 (i+1))
      = (∑ i ∈ Finset.range 23, stT186 (i+1)) + stT186 24 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 23
    simpa using h
  have hprev := st186_p23
  have hstep := st186_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p25 : ((2729770126961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT186 (i+1))
      = (∑ i ∈ Finset.range 24, stT186 (i+1)) + stT186 25 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 24
    simpa using h
  have hprev := st186_p24
  have hstep := st186_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p26 : ((347118478163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT186 (i+1))
      = (∑ i ∈ Finset.range 25, stT186 (i+1)) + stT186 26 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 25
    simpa using h
  have hprev := st186_p25
  have hstep := st186_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p27 : ((425431386863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT186 (i+1))
      = (∑ i ∈ Finset.range 26, stT186 (i+1)) + stT186 27 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 26
    simpa using h
  have hprev := st186_p26
  have hstep := st186_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p28 : ((664877503729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT186 (i+1))
      = (∑ i ∈ Finset.range 27, stT186 (i+1)) + stT186 28 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 27
    simpa using h
  have hprev := st186_p27
  have hstep := st186_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p29 : ((150400242791/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT186 (i+1))
      = (∑ i ∈ Finset.range 28, stT186 (i+1)) + stT186 29 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 28
    simpa using h
  have hprev := st186_p28
  have hstep := st186_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p30 : ((196887260133/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT186 (i+1))
      = (∑ i ∈ Finset.range 29, stT186 (i+1)) + stT186 30 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 29
    simpa using h
  have hprev := st186_p29
  have hstep := st186_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p31 : ((943530855423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT186 (i+1))
      = (∑ i ∈ Finset.range 30, stT186 (i+1)) + stT186 31 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 30
    simpa using h
  have hprev := st186_p30
  have hstep := st186_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p32 : ((822065376457/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT186 (i+1))
      = (∑ i ∈ Finset.range 31, stT186 (i+1)) + stT186 32 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 31
    simpa using h
  have hprev := st186_p31
  have hstep := st186_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p33 : ((7927059538081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT186 (i+1))
      = (∑ i ∈ Finset.range 32, stT186 (i+1)) + stT186 33 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 32
    simpa using h
  have hprev := st186_p32
  have hstep := st186_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p34 : ((6583638974869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT186 (i+1))
      = (∑ i ∈ Finset.range 33, stT186 (i+1)) + stT186 34 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 33
    simpa using h
  have hprev := st186_p33
  have hstep := st186_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p35 : ((4934228691433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT186 (i+1))
      = (∑ i ∈ Finset.range 34, stT186 (i+1)) + stT186 35 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 34
    simpa using h
  have hprev := st186_p34
  have hstep := st186_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p36 : ((553861282179/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT186 (i+1))
      = (∑ i ∈ Finset.range 35, stT186 (i+1)) + stT186 36 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 35
    simpa using h
  have hprev := st186_p35
  have hstep := st186_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p37 : ((1424534040559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT186 (i+1))
      = (∑ i ∈ Finset.range 36, stT186 (i+1)) + stT186 37 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 36
    simpa using h
  have hprev := st186_p36
  have hstep := st186_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p38 : ((1751653493659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT186 (i+1))
      = (∑ i ∈ Finset.range 37, stT186 (i+1)) + stT186 38 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 37
    simpa using h
  have hprev := st186_p37
  have hstep := st186_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p39 : ((3110122600551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT186 (i+1))
      = (∑ i ∈ Finset.range 38, stT186 (i+1)) + stT186 39 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 38
    simpa using h
  have hprev := st186_p38
  have hstep := st186_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p40 : ((1211331959079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT186 (i+1))
      = (∑ i ∈ Finset.range 39, stT186 (i+1)) + stT186 40 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 39
    simpa using h
  have hprev := st186_p39
  have hstep := st186_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p41 : ((57730495899/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT186 (i+1))
      = (∑ i ∈ Finset.range 40, stT186 (i+1)) + stT186 41 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 40
    simpa using h
  have hprev := st186_p40
  have hstep := st186_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p42 : ((1354449664843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT186 (i+1))
      = (∑ i ∈ Finset.range 41, stT186 (i+1)) + stT186 42 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 41
    simpa using h
  have hprev := st186_p41
  have hstep := st186_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p43 : ((5349681908961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT186 (i+1))
      = (∑ i ∈ Finset.range 42, stT186 (i+1)) + stT186 43 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 42
    simpa using h
  have hprev := st186_p42
  have hstep := st186_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p44 : ((218058823301/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT186 (i+1))
      = (∑ i ∈ Finset.range 43, stT186 (i+1)) + stT186 44 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 43
    simpa using h
  have hprev := st186_p43
  have hstep := st186_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p45 : ((3340837681571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT186 (i+1))
      = (∑ i ∈ Finset.range 44, stT186 (i+1)) + stT186 45 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 44
    simpa using h
  have hprev := st186_p44
  have hstep := st186_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p46 : ((2647384043911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT186 (i+1))
      = (∑ i ∈ Finset.range 45, stT186 (i+1)) + stT186 46 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 45
    simpa using h
  have hprev := st186_p45
  have hstep := st186_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p47 : ((363528368917/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT186 (i+1))
      = (∑ i ∈ Finset.range 46, stT186 (i+1)) + stT186 47 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 46
    simpa using h
  have hprev := st186_p46
  have hstep := st186_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p48 : ((6389786990047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT186 (i+1))
      = (∑ i ∈ Finset.range 47, stT186 (i+1)) + stT186 48 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 47
    simpa using h
  have hprev := st186_p47
  have hstep := st186_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p49 : ((5115193623067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT186 (i+1))
      = (∑ i ∈ Finset.range 48, stT186 (i+1)) + stT186 49 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 48
    simpa using h
  have hprev := st186_p48
  have hstep := st186_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p50 : ((3256995143577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT186 (i+1))
      = (∑ i ∈ Finset.range 49, stT186 (i+1)) + stT186 50 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 49
    simpa using h
  have hprev := st186_p49
  have hstep := st186_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p51 : ((5433190398709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT186 (i+1))
      = (∑ i ∈ Finset.range 50, stT186 (i+1)) + stT186 51 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 50
    simpa using h
  have hprev := st186_p50
  have hstep := st186_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p52 : ((5987780845459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT186 (i+1))
      = (∑ i ∈ Finset.range 51, stT186 (i+1)) + stT186 52 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 51
    simpa using h
  have hprev := st186_p51
  have hstep := st186_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p53 : ((5973822261287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT186 (i+1))
      = (∑ i ∈ Finset.range 52, stT186 (i+1)) + stT186 53 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 52
    simpa using h
  have hprev := st186_p52
  have hstep := st186_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p54 : ((5539196932163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT186 (i+1))
      = (∑ i ∈ Finset.range 53, stT186 (i+1)) + stT186 54 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 53
    simpa using h
  have hprev := st186_p53
  have hstep := st186_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p55 : ((3148221489087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT186 (i+1))
      = (∑ i ∈ Finset.range 54, stT186 (i+1)) + stT186 55 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 54
    simpa using h
  have hprev := st186_p54
  have hstep := st186_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p56 : ((66650010219/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT186 (i+1))
      = (∑ i ∈ Finset.range 55, stT186 (i+1)) + stT186 56 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 55
    simpa using h
  have hprev := st186_p55
  have hstep := st186_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p57 : ((400906483389/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT186 (i+1))
      = (∑ i ∈ Finset.range 56, stT186 (i+1)) + stT186 57 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 56
    simpa using h
  have hprev := st186_p56
  have hstep := st186_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p58 : ((329714725219/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT186 (i+1))
      = (∑ i ∈ Finset.range 57, stT186 (i+1)) + stT186 58 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 57
    simpa using h
  have hprev := st186_p57
  have hstep := st186_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p59 : ((100444546759/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT186 (i+1))
      = (∑ i ∈ Finset.range 58, stT186 (i+1)) + stT186 59 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 58
    simpa using h
  have hprev := st186_p58
  have hstep := st186_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p60 : ((5294364815871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT186 (i+1))
      = (∑ i ∈ Finset.range 59, stT186 (i+1)) + stT186 60 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 59
    simpa using h
  have hprev := st186_p59
  have hstep := st186_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p61 : ((6375400004159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT186 (i+1))
      = (∑ i ∈ Finset.range 60, stT186 (i+1)) + stT186 61 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 60
    simpa using h
  have hprev := st186_p60
  have hstep := st186_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p62 : ((5389861942133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT186 (i+1))
      = (∑ i ∈ Finset.range 61, stT186 (i+1)) + stT186 62 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 61
    simpa using h
  have hprev := st186_p61
  have hstep := st186_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p63 : ((388945048627/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT186 (i+1))
      = (∑ i ∈ Finset.range 62, stT186 (i+1)) + stT186 63 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 62
    simpa using h
  have hprev := st186_p62
  have hstep := st186_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p64 : ((5612494039531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT186 (i+1))
      = (∑ i ∈ Finset.range 63, stT186 (i+1)) + stT186 64 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 63
    simpa using h
  have hprev := st186_p63
  have hstep := st186_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p65 : ((118446083843/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT186 (i+1))
      = (∑ i ∈ Finset.range 64, stT186 (i+1)) + stT186 65 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 64
    simpa using h
  have hprev := st186_p64
  have hstep := st186_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p66 : ((2991473200637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT186 (i+1))
      = (∑ i ∈ Finset.range 65, stT186 (i+1)) + stT186 66 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 65
    simpa using h
  have hprev := st186_p65
  have hstep := st186_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p67 : ((2757015269797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT186 (i+1))
      = (∑ i ∈ Finset.range 66, stT186 (i+1)) + stT186 67 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 66
    simpa using h
  have hprev := st186_p66
  have hstep := st186_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p68 : ((636670324709/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT186 (i+1))
      = (∑ i ∈ Finset.range 67, stT186 (i+1)) + stT186 68 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 67
    simpa using h
  have hprev := st186_p67
  have hstep := st186_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p69 : ((1048393575973/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT186 (i+1))
      = (∑ i ∈ Finset.range 68, stT186 (i+1)) + stT186 69 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 68
    simpa using h
  have hprev := st186_p68
  have hstep := st186_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p70 : ((6431095436153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT186 (i+1))
      = (∑ i ∈ Finset.range 69, stT186 (i+1)) + stT186 70 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 69
    simpa using h
  have hprev := st186_p69
  have hstep := st186_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p71 : ((5454118692023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT186 (i+1))
      = (∑ i ∈ Finset.range 70, stT186 (i+1)) + stT186 71 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 70
    simpa using h
  have hprev := st186_p70
  have hstep := st186_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p72 : ((2970969285871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT186 (i+1))
      = (∑ i ∈ Finset.range 71, stT186 (i+1)) + stT186 72 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 71
    simpa using h
  have hprev := st186_p71
  have hstep := st186_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p73 : ((191121188503/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT186 (i+1))
      = (∑ i ∈ Finset.range 72, stT186 (i+1)) + stT186 73 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 72
    simpa using h
  have hprev := st186_p72
  have hstep := st186_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p74 : ((2657411053129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT186 (i+1))
      = (∑ i ∈ Finset.range 73, stT186 (i+1)) + stT186 74 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 73
    simpa using h
  have hprev := st186_p73
  have hstep := st186_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p75 : ((3226821335929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT186 (i+1))
      = (∑ i ∈ Finset.range 74, stT186 (i+1)) + stT186 75 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 74
    simpa using h
  have hprev := st186_p74
  have hstep := st186_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p76 : ((545374308419/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT186 (i+1))
      = (∑ i ∈ Finset.range 75, stT186 (i+1)) + stT186 76 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 75
    simpa using h
  have hprev := st186_p75
  have hstep := st186_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p77 : ((233707929917/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT186 (i+1))
      = (∑ i ∈ Finset.range 76, stT186 (i+1)) + stT186 77 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 76
    simpa using h
  have hprev := st186_p76
  have hstep := st186_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p78 : ((6276469037517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT186 (i+1))
      = (∑ i ∈ Finset.range 77, stT186 (i+1)) + stT186 78 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 77
    simpa using h
  have hprev := st186_p77
  have hstep := st186_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p79 : ((5242544667981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT186 (i+1))
      = (∑ i ∈ Finset.range 78, stT186 (i+1)) + stT186 79 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 78
    simpa using h
  have hprev := st186_p78
  have hstep := st186_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p80 : ((3136896296211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT186 (i+1))
      = (∑ i ∈ Finset.range 79, stT186 (i+1)) + stT186 80 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 79
    simpa using h
  have hprev := st186_p79
  have hstep := st186_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p81 : ((117994601419/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT186 (i+1))
      = (∑ i ∈ Finset.range 80, stT186 (i+1)) + stT186 81 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 80
    simpa using h
  have hprev := st186_p80
  have hstep := st186_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p82 : ((2677378927581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT186 (i+1))
      = (∑ i ∈ Finset.range 81, stT186 (i+1)) + stT186 82 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 81
    simpa using h
  have hprev := st186_p81
  have hstep := st186_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p83 : ((128738769399/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT186 (i+1))
      = (∑ i ∈ Finset.range 82, stT186 (i+1)) + stT186 83 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 82
    simpa using h
  have hprev := st186_p82
  have hstep := st186_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p84 : ((563579036219/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT186 (i+1))
      = (∑ i ∈ Finset.range 83, stT186 (i+1)) + stT186 84 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 83
    simpa using h
  have hprev := st186_p83
  have hstep := st186_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p85 : ((2755165359493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT186 (i+1))
      = (∑ i ∈ Finset.range 84, stT186 (i+1)) + stT186 85 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 84
    simpa using h
  have hprev := st186_p84
  have hstep := st186_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p86 : ((6462337102571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT186 (i+1))
      = (∑ i ∈ Finset.range 85, stT186 (i+1)) + stT186 86 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 85
    simpa using h
  have hprev := st186_p85
  have hstep := st186_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p87 : ((5522694384851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT186 (i+1))
      = (∑ i ∈ Finset.range 86, stT186 (i+1)) + stT186 87 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 86
    simpa using h
  have hprev := st186_p86
  have hstep := st186_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p88 : ((2789268476003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT186 (i+1))
      = (∑ i ∈ Finset.range 87, stT186 (i+1)) + stT186 88 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 87
    simpa using h
  have hprev := st186_p87
  have hstep := st186_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p89 : ((6463169108323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT186 (i+1))
      = (∑ i ∈ Finset.range 88, stT186 (i+1)) + stT186 89 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 88
    simpa using h
  have hprev := st186_p88
  have hstep := st186_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p90 : ((5528135912673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT186 (i+1))
      = (∑ i ∈ Finset.range 89, stT186 (i+1)) + stT186 90 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 89
    simpa using h
  have hprev := st186_p89
  have hstep := st186_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p91 : ((5532787148781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT186 (i+1))
      = (∑ i ∈ Finset.range 90, stT186 (i+1)) + stT186 91 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 90
    simpa using h
  have hprev := st186_p90
  have hstep := st186_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p92 : ((6463909244553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT186 (i+1))
      = (∑ i ∈ Finset.range 91, stT186 (i+1)) + stT186 92 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 91
    simpa using h
  have hprev := st186_p91
  have hstep := st186_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p93 : ((5647396648521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT186 (i+1))
      = (∑ i ∈ Finset.range 92, stT186 (i+1)) + stT186 93 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 92
    simpa using h
  have hprev := st186_p92
  have hstep := st186_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p94 : ((5396424858949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT186 (i+1))
      = (∑ i ∈ Finset.range 93, stT186 (i+1)) + stT186 94 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 93
    simpa using h
  have hprev := st186_p93
  have hstep := st186_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p95 : ((6410564098807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT186 (i+1))
      = (∑ i ∈ Finset.range 94, stT186 (i+1)) + stT186 95 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 94
    simpa using h
  have hprev := st186_p94
  have hstep := st186_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p96 : ((2947895211587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT186 (i+1))
      = (∑ i ∈ Finset.range 95, stT186 (i+1)) + stT186 96 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 95
    simpa using h
  have hprev := st186_p95
  have hstep := st186_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p97 : ((5252952915187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT186 (i+1))
      = (∑ i ∈ Finset.range 96, stT186 (i+1)) + stT186 97 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 96
    simpa using h
  have hprev := st186_p96
  have hstep := st186_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p98 : ((6202294774939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT186 (i+1))
      = (∑ i ∈ Finset.range 97, stT186 (i+1)) + stT186 98 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 97
    simpa using h
  have hprev := st186_p97
  have hstep := st186_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p99 : ((6233446901791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT186 (i+1))
      = (∑ i ∈ Finset.range 98, stT186 (i+1)) + stT186 99 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 98
    simpa using h
  have hprev := st186_p98
  have hstep := st186_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p100 : ((5268964901791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT186 (i+1))
      = (∑ i ∈ Finset.range 99, stT186 (i+1)) + stT186 100 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 99
    simpa using h
  have hprev := st186_p99
  have hstep := st186_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p101 : ((723359336879/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT186 (i+1))
      = (∑ i ∈ Finset.range 100, stT186 (i+1)) + stT186 101 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 100
    simpa using h
  have hprev := st186_p100
  have hstep := st186_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p102 : ((6470090977237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT186 (i+1))
      = (∑ i ∈ Finset.range 101, stT186 (i+1)) + stT186 102 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 101
    simpa using h
  have hprev := st186_p101
  have hstep := st186_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p103 : ((5613849060537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT186 (i+1))
      = (∑ i ∈ Finset.range 102, stT186 (i+1)) + stT186 103 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 102
    simpa using h
  have hprev := st186_p102
  have hstep := st186_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p104 : ((83313506273/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT186 (i+1))
      = (∑ i ∈ Finset.range 103, stT186 (i+1)) + stT186 104 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 103
    simpa using h
  have hprev := st186_p103
  have hstep := st186_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p105 : ((788076645109/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT186 (i+1))
      = (∑ i ∈ Finset.range 104, stT186 (i+1)) + stT186 105 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 104
    simpa using h
  have hprev := st186_p104
  have hstep := st186_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p106 : ((1549496831591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT186 (i+1))
      = (∑ i ∈ Finset.range 105, stT186 (i+1)) + stT186 106 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 105
    simpa using h
  have hprev := st186_p105
  have hstep := st186_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p107 : ((1054075414593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT186 (i+1))
      = (∑ i ∈ Finset.range 106, stT186 (i+1)) + stT186 107 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 106
    simpa using h
  have hprev := st186_p106
  have hstep := st186_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p108 : ((1136925909393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT186 (i+1))
      = (∑ i ∈ Finset.range 107, stT186 (i+1)) + stT186 108 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 107
    simpa using h
  have hprev := st186_p107
  have hstep := st186_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p109 : ((1296244939277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT186 (i+1))
      = (∑ i ∈ Finset.range 108, stT186 (i+1)) + stT186 109 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 108
    simpa using h
  have hprev := st186_p108
  have hstep := st186_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p110 : ((365939330623/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT186 (i+1))
      = (∑ i ∈ Finset.range 109, stT186 (i+1)) + stT186 110 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 109
    simpa using h
  have hprev := st186_p109
  have hstep := st186_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p111 : ((1303417485289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT186 (i+1))
      = (∑ i ∈ Finset.range 110, stT186 (i+1)) + stT186 111 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 110
    simpa using h
  have hprev := st186_p110
  have hstep := st186_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p112 : ((1193796720819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT186 (i+1))
      = (∑ i ∈ Finset.range 111, stT186 (i+1)) + stT186 112 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 111
    simpa using h
  have hprev := st186_p111
  have hstep := st186_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p113 : ((1294036645571/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT186 (i+1))
      = (∑ i ∈ Finset.range 112, stT186 (i+1)) + stT186 113 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 112
    simpa using h
  have hprev := st186_p112
  have hstep := st186_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p114 : ((5645511762167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT186 (i+1))
      = (∑ i ∈ Finset.range 113, stT186 (i+1)) + stT186 114 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 113
    simpa using h
  have hprev := st186_p113
  have hstep := st186_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p115 : ((5248024045877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT186 (i+1))
      = (∑ i ∈ Finset.range 114, stT186 (i+1)) + stT186 115 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 114
    simpa using h
  have hprev := st186_p114
  have hstep := st186_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p116 : ((6102905324213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT186 (i+1))
      = (∑ i ∈ Finset.range 115, stT186 (i+1)) + stT186 116 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 115
    simpa using h
  have hprev := st186_p115
  have hstep := st186_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p117 : ((6441405452213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT186 (i+1))
      = (∑ i ∈ Finset.range 116, stT186 (i+1)) + stT186 117 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 116
    simpa using h
  have hprev := st186_p116
  have hstep := st186_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p118 : ((2790340817919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT186 (i+1))
      = (∑ i ∈ Finset.range 117, stT186 (i+1)) + stT186 118 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 117
    simpa using h
  have hprev := st186_p117
  have hstep := st186_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p119 : ((525436245941/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT186 (i+1))
      = (∑ i ∈ Finset.range 118, stT186 (i+1)) + stT186 119 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 118
    simpa using h
  have hprev := st186_p118
  have hstep := st186_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p120 : ((305133851581/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT186 (i+1))
      = (∑ i ∈ Finset.range 119, stT186 (i+1)) + stT186 120 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 119
    simpa using h
  have hprev := st186_p119
  have hstep := st186_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p121 : ((323058742747/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT186 (i+1))
      = (∑ i ∈ Finset.range 120, stT186 (i+1)) + stT186 121 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 120
    simpa using h
  have hprev := st186_p120
  have hstep := st186_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p122 : ((1411018693553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT186 (i+1))
      = (∑ i ∈ Finset.range 121, stT186 (i+1)) + stT186 122 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 121
    simpa using h
  have hprev := st186_p121
  have hstep := st186_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p123 : ((2606760518761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT186 (i+1))
      = (∑ i ∈ Finset.range 122, stT186 (i+1)) + stT186 123 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 122
    simpa using h
  have hprev := st186_p122
  have hstep := st186_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p124 : ((597315045461/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT186 (i+1))
      = (∑ i ∈ Finset.range 123, stT186 (i+1)) + stT186 124 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 123
    simpa using h
  have hprev := st186_p123
  have hstep := st186_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p125 : ((650673877/1000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT186 (i+1))
      = (∑ i ∈ Finset.range 124, stT186 (i+1)) + stT186 125 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 124
    simpa using h
  have hprev := st186_p124
  have hstep := st186_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p126 : ((5841649225369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT186 (i+1))
      = (∑ i ∈ Finset.range 125, stT186 (i+1)) + stT186 126 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 125
    simpa using h
  have hprev := st186_p125
  have hstep := st186_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p127 : ((1296932529679/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT186 (i+1))
      = (∑ i ∈ Finset.range 126, stT186 (i+1)) + stT186 127 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 126
    simpa using h
  have hprev := st186_p126
  have hstep := st186_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p128 : ((1141740449879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT186 (i+1))
      = (∑ i ∈ Finset.range 127, stT186 (i+1)) + stT186 128 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 127
    simpa using h
  have hprev := st186_p127
  have hstep := st186_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p129 : ((1295663008049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT186 (i+1))
      = (∑ i ∈ Finset.range 128, stT186 (i+1)) + stT186 129 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 128
    simpa using h
  have hprev := st186_p128
  have hstep := st186_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p130 : ((6159002415997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT186 (i+1))
      = (∑ i ∈ Finset.range 129, stT186 (i+1)) + stT186 130 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 129
    simpa using h
  have hprev := st186_p129
  have hstep := st186_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p131 : ((1326921089803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT186 (i+1))
      = (∑ i ∈ Finset.range 130, stT186 (i+1)) + stT186 131 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 130
    simpa using h
  have hprev := st186_p130
  have hstep := st186_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p132 : ((671145526949/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT186 (i+1))
      = (∑ i ∈ Finset.range 131, stT186 (i+1)) + stT186 132 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 131
    simpa using h
  have hprev := st186_p131
  have hstep := st186_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p133 : ((6232214278363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT186 (i+1))
      = (∑ i ∈ Finset.range 132, stT186 (i+1)) + stT186 133 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 132
    simpa using h
  have hprev := st186_p132
  have hstep := st186_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p134 : ((1293152025659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT186 (i+1))
      = (∑ i ∈ Finset.range 133, stT186 (i+1)) + stT186 134 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 133
    simpa using h
  have hprev := st186_p133
  have hstep := st186_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p135 : ((35594811341/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT186 (i+1))
      = (∑ i ∈ Finset.range 134, stT186 (i+1)) + stT186 135 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 134
    simpa using h
  have hprev := st186_p134
  have hstep := st186_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p136 : ((516951803063/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT186 (i+1))
      = (∑ i ∈ Finset.range 135, stT186 (i+1)) + stT186 136 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 135
    simpa using h
  have hprev := st186_p135
  have hstep := st186_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p137 : ((5721729114509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT186 (i+1))
      = (∑ i ∈ Finset.range 136, stT186 (i+1)) + stT186 137 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 136
    simpa using h
  have hprev := st186_p136
  have hstep := st186_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p138 : ((6474859132877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT186 (i+1))
      = (∑ i ∈ Finset.range 137, stT186 (i+1)) + stT186 138 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 137
    simpa using h
  have hprev := st186_p137
  have hstep := st186_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p139 : ((6259257970967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT186 (i+1))
      = (∑ i ∈ Finset.range 138, stT186 (i+1)) + stT186 139 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 138
    simpa using h
  have hprev := st186_p138
  have hstep := st186_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p140 : ((5414221292667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT186 (i+1))
      = (∑ i ∈ Finset.range 139, stT186 (i+1)) + stT186 140 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 139
    simpa using h
  have hprev := st186_p139
  have hstep := st186_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p141 : ((1044854613383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT186 (i+1))
      = (∑ i ∈ Finset.range 140, stT186 (i+1)) + stT186 141 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 140
    simpa using h
  have hprev := st186_p140
  have hstep := st186_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p142 : ((298356014201/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT186 (i+1))
      = (∑ i ∈ Finset.range 141, stT186 (i+1)) + stT186 142 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 141
    simpa using h
  have hprev := st186_p141
  have hstep := st186_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p143 : ((3268325212149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT186 (i+1))
      = (∑ i ∈ Finset.range 142, stT186 (i+1)) + stT186 143 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 142
    simpa using h
  have hprev := st186_p142
  have hstep := st186_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p144 : ((305162628879/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT186 (i+1))
      = (∑ i ∈ Finset.range 143, stT186 (i+1)) + stT186 144 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 143
    simpa using h
  have hprev := st186_p143
  have hstep := st186_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p145 : ((106027537119/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT186 (i+1))
      = (∑ i ∈ Finset.range 144, stT186 (i+1)) + stT186 145 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 144
    simpa using h
  have hprev := st186_p144
  have hstep := st186_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p146 : ((1319306207513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT186 (i+1))
      = (∑ i ∈ Finset.range 145, stT186 (i+1)) + stT186 146 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 145
    simpa using h
  have hprev := st186_p145
  have hstep := st186_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p147 : ((757172707449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT186 (i+1))
      = (∑ i ∈ Finset.range 146, stT186 (i+1)) + stT186 147 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 146
    simpa using h
  have hprev := st186_p146
  have hstep := st186_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p148 : ((818536203537/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT186 (i+1))
      = (∑ i ∈ Finset.range 147, stT186 (i+1)) + stT186 148 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 147
    simpa using h
  have hprev := st186_p147
  have hstep := st186_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p149 : ((6077290213/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT186 (i+1))
      = (∑ i ∈ Finset.range 148, stT186 (i+1)) + stT186 149 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 148
    simpa using h
  have hprev := st186_p148
  have hstep := st186_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p150 : ((661733892433/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT186 (i+1))
      = (∑ i ∈ Finset.range 149, stT186 (i+1)) + stT186 150 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 149
    simpa using h
  have hprev := st186_p149
  have hstep := st186_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p151 : ((2626941587791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT186 (i+1))
      = (∑ i ∈ Finset.range 150, stT186 (i+1)) + stT186 151 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 150
    simpa using h
  have hprev := st186_p150
  have hstep := st186_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p152 : ((750421297099/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT186 (i+1))
      = (∑ i ∈ Finset.range 151, stT186 (i+1)) + stT186 152 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 151
    simpa using h
  have hprev := st186_p151
  have hstep := st186_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p153 : ((102350349341/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT186 (i+1))
      = (∑ i ∈ Finset.range 152, stT186 (i+1)) + stT186 153 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 152
    simpa using h
  have hprev := st186_p152
  have hstep := st186_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p154 : ((3093278102733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT186 (i+1))
      = (∑ i ∈ Finset.range 153, stT186 (i+1)) + stT186 154 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 153
    simpa using h
  have hprev := st186_p153
  have hstep := st186_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p155 : ((2693716313733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT186 (i+1))
      = (∑ i ∈ Finset.range 154, stT186 (i+1)) + stT186 155 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 154
    simpa using h
  have hprev := st186_p154
  have hstep := st186_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p156 : ((64642886183/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT186 (i+1))
      = (∑ i ∈ Finset.range 155, stT186 (i+1)) + stT186 156 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 155
    simpa using h
  have hprev := st186_p155
  have hstep := st186_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p157 : ((1451027594699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT186 (i+1))
      = (∑ i ∈ Finset.range 156, stT186 (i+1)) + stT186 157 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 156
    simpa using h
  have hprev := st186_p156
  have hstep := st186_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p158 : ((811533795753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT186 (i+1))
      = (∑ i ∈ Finset.range 157, stT186 (i+1)) + stT186 158 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 157
    simpa using h
  have hprev := st186_p157
  have hstep := st186_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p159 : ((159769944413/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT186 (i+1))
      = (∑ i ∈ Finset.range 158, stT186 (i+1)) + stT186 159 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 158
    simpa using h
  have hprev := st186_p158
  have hstep := st186_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p160 : ((563019433237/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT186 (i+1))
      = (∑ i ∈ Finset.range 159, stT186 (i+1)) + stT186 160 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 159
    simpa using h
  have hprev := st186_p159
  have hstep := st186_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p161 : ((5129514507069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT186 (i+1))
      = (∑ i ∈ Finset.range 160, stT186 (i+1)) + stT186 161 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 160
    simpa using h
  have hprev := st186_p160
  have hstep := st186_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p162 : ((1096131786117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT186 (i+1))
      = (∑ i ∈ Finset.range 161, stT186 (i+1)) + stT186 162 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 161
    simpa using h
  have hprev := st186_p161
  have hstep := st186_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p163 : ((1252667393681/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT186 (i+1))
      = (∑ i ∈ Finset.range 162, stT186 (i+1)) + stT186 163 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 162
    simpa using h
  have hprev := st186_p162
  have hstep := st186_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p164 : ((6564476370001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT186 (i+1))
      = (∑ i ∈ Finset.range 163, stT186 (i+1)) + stT186 164 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 163
    simpa using h
  have hprev := st186_p163
  have hstep := st186_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p165 : ((3021270917969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT186 (i+1))
      = (∑ i ∈ Finset.range 164, stT186 (i+1)) + stT186 165 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 164
    simpa using h
  have hprev := st186_p164
  have hstep := st186_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p166 : ((2649137559509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT186 (i+1))
      = (∑ i ∈ Finset.range 165, stT186 (i+1)) + stT186 166 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 165
    simpa using h
  have hprev := st186_p165
  have hstep := st186_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p167 : ((2585239042709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT186 (i+1))
      = (∑ i ∈ Finset.range 166, stT186 (i+1)) + stT186 167 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 166
    simpa using h
  have hprev := st186_p166
  have hstep := st186_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p168 : ((2897780560067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT186 (i+1))
      = (∑ i ∈ Finset.range 167, stT186 (i+1)) + stT186 168 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 167
    simpa using h
  have hprev := st186_p167
  have hstep := st186_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p169 : ((1619664147721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT186 (i+1))
      = (∑ i ∈ Finset.range 168, stT186 (i+1)) + stT186 169 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 168
    simpa using h
  have hprev := st186_p168
  have hstep := st186_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p170 : ((3237696960887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT186 (i+1))
      = (∑ i ∈ Finset.range 169, stT186 (i+1)) + stT186 170 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 169
    simpa using h
  have hprev := st186_p169
  have hstep := st186_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p171 : ((2897767450087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT186 (i+1))
      = (∑ i ∈ Finset.range 170, stT186 (i+1)) + stT186 171 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 170
    simpa using h
  have hprev := st186_p170
  have hstep := st186_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p172 : ((5170024530117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT186 (i+1))
      = (∑ i ∈ Finset.range 171, stT186 (i+1)) + stT186 172 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 171
    simpa using h
  have hprev := st186_p171
  have hstep := st186_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p173 : ((657278624299/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT186 (i+1))
      = (∑ i ∈ Finset.range 172, stT186 (i+1)) + stT186 173 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 172
    simpa using h
  have hprev := st186_p172
  have hstep := st186_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p174 : ((1490381780591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT186 (i+1))
      = (∑ i ∈ Finset.range 173, stT186 (i+1)) + stT186 174 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 173
    simpa using h
  have hprev := st186_p173
  have hstep := st186_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p175 : ((1636904060759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT186 (i+1))
      = (∑ i ∈ Finset.range 174, stT186 (i+1)) + stT186 175 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 174
    simpa using h
  have hprev := st186_p174
  have hstep := st186_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p176 : ((6418179574493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT186 (i+1))
      = (∑ i ∈ Finset.range 175, stT186 (i+1)) + stT186 176 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 175
    simpa using h
  have hprev := st186_p175
  have hstep := st186_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p177 : ((5710642227041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT186 (i+1))
      = (∑ i ∈ Finset.range 176, stT186 (i+1)) + stT186 177 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 176
    simpa using h
  have hprev := st186_p176
  have hstep := st186_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p178 : ((5139000404261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT186 (i+1))
      = (∑ i ∈ Finset.range 177, stT186 (i+1)) + stT186 178 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 177
    simpa using h
  have hprev := st186_p177
  have hstep := st186_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p179 : ((164651984323/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT186 (i+1))
      = (∑ i ∈ Finset.range 178, stT186 (i+1)) + stT186 179 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 178
    simpa using h
  have hprev := st186_p178
  have hstep := st186_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p180 : ((5966425590381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT186 (i+1))
      = (∑ i ∈ Finset.range 179, stT186 (i+1)) + stT186 180 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 179
    simpa using h
  have hprev := st186_p179
  have hstep := st186_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p181 : ((6548735489273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT186 (i+1))
      = (∑ i ∈ Finset.range 180, stT186 (i+1)) + stT186 181 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 180
    simpa using h
  have hprev := st186_p180
  have hstep := st186_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p182 : ((6456608491773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT186 (i+1))
      = (∑ i ∈ Finset.range 181, stT186 (i+1)) + stT186 182 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 181
    simpa using h
  have hprev := st186_p181
  have hstep := st186_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p183 : ((5783738319271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT186 (i+1))
      = (∑ i ∈ Finset.range 182, stT186 (i+1)) + stT186 183 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 182
    simpa using h
  have hprev := st186_p182
  have hstep := st186_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p184 : ((5169722007951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT186 (i+1))
      = (∑ i ∈ Finset.range 183, stT186 (i+1)) + stT186 184 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 183
    simpa using h
  have hprev := st186_p183
  have hstep := st186_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p185 : ((5187267154847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT186 (i+1))
      = (∑ i ∈ Finset.range 184, stT186 (i+1)) + stT186 185 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 184
    simpa using h
  have hprev := st186_p184
  have hstep := st186_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p186 : ((2907273748821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT186 (i+1))
      = (∑ i ∈ Finset.range 185, stT186 (i+1)) + stT186 186 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 185
    simpa using h
  have hprev := st186_p185
  have hstep := st186_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p187 : ((3235990019357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT186 (i+1))
      = (∑ i ∈ Finset.range 186, stT186 (i+1)) + stT186 187 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 186
    simpa using h
  have hprev := st186_p186
  have hstep := st186_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p188 : ((3281675239379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT186 (i+1))
      = (∑ i ∈ Finset.range 187, stT186 (i+1)) + stT186 188 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 187
    simpa using h
  have hprev := st186_p187
  have hstep := st186_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p189 : ((1202309884313/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT186 (i+1))
      = (∑ i ∈ Finset.range 188, stT186 (i+1)) + stT186 189 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 188
    simpa using h
  have hprev := st186_p188
  have hstep := st186_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p190 : ((5312671310293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT186 (i+1))
      = (∑ i ∈ Finset.range 189, stT186 (i+1)) + stT186 190 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 189
    simpa using h
  have hprev := st186_p189
  have hstep := st186_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p191 : ((1270810218217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT186 (i+1))
      = (∑ i ∈ Finset.range 190, stT186 (i+1)) + stT186 191 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 190
    simpa using h
  have hprev := st186_p190
  have hstep := st186_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p192 : ((344950027661/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT186 (i+1))
      = (∑ i ∈ Finset.range 191, stT186 (i+1)) + stT186 192 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 191
    simpa using h
  have hprev := st186_p191
  have hstep := st186_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p193 : ((6238279071831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT186 (i+1))
      = (∑ i ∈ Finset.range 192, stT186 (i+1)) + stT186 193 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 192
    simpa using h
  have hprev := st186_p192
  have hstep := st186_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p194 : ((6622912147087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT186 (i+1))
      = (∑ i ∈ Finset.range 193, stT186 (i+1)) + stT186 194 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 193
    simpa using h
  have hprev := st186_p193
  have hstep := st186_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p195 : ((6350043687487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT186 (i+1))
      = (∑ i ∈ Finset.range 194, stT186 (i+1)) + stT186 195 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 194
    simpa using h
  have hprev := st186_p194
  have hstep := st186_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p196 : ((5654291266329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT186 (i+1))
      = (∑ i ∈ Finset.range 195, stT186 (i+1)) + stT186 196 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 195
    simpa using h
  have hprev := st186_p195
  have hstep := st186_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p197 : ((255885078493/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT186 (i+1))
      = (∑ i ∈ Finset.range 196, stT186 (i+1)) + stT186 197 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 196
    simpa using h
  have hprev := st186_p196
  have hstep := st186_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p198 : ((2590426519269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT186 (i+1))
      = (∑ i ∈ Finset.range 197, stT186 (i+1)) + stT186 198 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 197
    simpa using h
  have hprev := st186_p197
  have hstep := st186_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p199 : ((723387249259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT186 (i+1))
      = (∑ i ∈ Finset.range 198, stT186 (i+1)) + stT186 199 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 198
    simpa using h
  have hprev := st186_p198
  have hstep := st186_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p200 : ((644171763701/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT186 (i+1))
      = (∑ i ∈ Finset.range 199, stT186 (i+1)) + stT186 200 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 199
    simpa using h
  have hprev := st186_p199
  have hstep := st186_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p201 : ((1323990676219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT186 (i+1))
      = (∑ i ∈ Finset.range 200, stT186 (i+1)) + stT186 201 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 200
    simpa using h
  have hprev := st186_p200
  have hstep := st186_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p202 : ((6184346712521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT186 (i+1))
      = (∑ i ∈ Finset.range 201, stT186 (i+1)) + stT186 202 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 201
    simpa using h
  have hprev := st186_p201
  have hstep := st186_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p203 : ((2741265368671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT186 (i+1))
      = (∑ i ∈ Finset.range 202, stT186 (i+1)) + stT186 203 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 202
    simpa using h
  have hprev := st186_p202
  have hstep := st186_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p204 : ((5063523654341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT186 (i+1))
      = (∑ i ∈ Finset.range 203, stT186 (i+1)) + stT186 204 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 203
    simpa using h
  have hprev := st186_p203
  have hstep := st186_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p205 : ((5248451156021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT186 (i+1))
      = (∑ i ∈ Finset.range 204, stT186 (i+1)) + stT186 205 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 204
    simpa using h
  have hprev := st186_p204
  have hstep := st186_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p206 : ((5890783243381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT186 (i+1))
      = (∑ i ∈ Finset.range 205, stT186 (i+1)) + stT186 206 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 205
    simpa using h
  have hprev := st186_p205
  have hstep := st186_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p207 : ((6499686299213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT186 (i+1))
      = (∑ i ∈ Finset.range 206, stT186 (i+1)) + stT186 207 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 206
    simpa using h
  have hprev := st186_p206
  have hstep := st186_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p208 : ((6617876228213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT186 (i+1))
      = (∑ i ∈ Finset.range 207, stT186 (i+1)) + stT186 208 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 207
    simpa using h
  have hprev := st186_p207
  have hstep := st186_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p209 : ((770168127491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT186 (i+1))
      = (∑ i ∈ Finset.range 208, stT186 (i+1)) + stT186 209 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 208
    simpa using h
  have hprev := st186_p208
  have hstep := st186_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p210 : ((683967152969/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT186 (i+1))
      = (∑ i ∈ Finset.range 209, stT186 (i+1)) + stT186 210 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 209
    simpa using h
  have hprev := st186_p209
  have hstep := st186_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p211 : ((1263851413857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT186 (i+1))
      = (∑ i ∈ Finset.range 210, stT186 (i+1)) + stT186 211 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 210
    simpa using h
  have hprev := st186_p210
  have hstep := st186_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p212 : ((2605983489471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT186 (i+1))
      = (∑ i ∈ Finset.range 211, stT186 (i+1)) + stT186 212 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 211
    simpa using h
  have hprev := st186_p211
  have hstep := st186_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p213 : ((582422425341/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT186 (i+1))
      = (∑ i ∈ Finset.range 212, stT186 (i+1)) + stT186 213 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 212
    simpa using h
  have hprev := st186_p212
  have hstep := st186_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p214 : ((322613808759/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT186 (i+1))
      = (∑ i ∈ Finset.range 213, stT186 (i+1)) + stT186 214 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 213
    simpa using h
  have hprev := st186_p213
  have hstep := st186_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p215 : ((20788858107/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT186 (i+1))
      = (∑ i ∈ Finset.range 214, stT186 (i+1)) + stT186 215 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 214
    simpa using h
  have hprev := st186_p214
  have hstep := st186_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p216 : ((3143994603159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT186 (i+1))
      = (∑ i ∈ Finset.range 215, stT186 (i+1)) + stT186 216 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 215
    simpa using h
  have hprev := st186_p215
  have hstep := st186_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p217 : ((5616381372863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT186 (i+1))
      = (∑ i ∈ Finset.range 216, stT186 (i+1)) + stT186 217 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 216
    simpa using h
  have hprev := st186_p216
  have hstep := st186_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p218 : ((1020427279957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT186 (i+1))
      = (∑ i ∈ Finset.range 217, stT186 (i+1)) + stT186 218 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 217
    simpa using h
  have hprev := st186_p217
  have hstep := st186_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p219 : ((5094769504109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT186 (i+1))
      = (∑ i ∈ Finset.range 218, stT186 (i+1)) + stT186 219 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 218
    simpa using h
  have hprev := st186_p218
  have hstep := st186_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p220 : ((5595207195839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT186 (i+1))
      = (∑ i ∈ Finset.range 219, stT186 (i+1)) + stT186 220 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 219
    simpa using h
  have hprev := st186_p219
  have hstep := st186_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p221 : ((6263833073759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT186 (i+1))
      = (∑ i ∈ Finset.range 220, stT186 (i+1)) + stT186 221 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 220
    simpa using h
  have hprev := st186_p220
  have hstep := st186_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p222 : ((6654749228271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT186 (i+1))
      = (∑ i ∈ Finset.range 221, stT186 (i+1)) + stT186 222 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 221
    simpa using h
  have hprev := st186_p221
  have hstep := st186_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p223 : ((6512400388471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT186 (i+1))
      = (∑ i ∈ Finset.range 222, stT186 (i+1)) + stT186 223 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 222
    simpa using h
  have hprev := st186_p222
  have hstep := st186_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p224 : ((1186800704843/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT186 (i+1))
      = (∑ i ∈ Finset.range 223, stT186 (i+1)) + stT186 224 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 223
    simpa using h
  have hprev := st186_p223
  have hstep := st186_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p225 : ((5297891206159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT186 (i+1))
      = (∑ i ∈ Finset.range 224, stT186 (i+1)) + stT186 225 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 224
    simpa using h
  have hprev := st186_p224
  have hstep := st186_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p226 : ((1002679931703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT186 (i+1))
      = (∑ i ∈ Finset.range 225, stT186 (i+1)) + stT186 226 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 225
    simpa using h
  have hprev := st186_p225
  have hstep := st186_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p227 : ((105182795613/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT186 (i+1))
      = (∑ i ∈ Finset.range 226, stT186 (i+1)) + stT186 227 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 226
    simpa using h
  have hprev := st186_p226
  have hstep := st186_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p228 : ((2937809679237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT186 (i+1))
      = (∑ i ∈ Finset.range 227, stT186 (i+1)) + stT186 228 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 227
    simpa using h
  have hprev := st186_p227
  have hstep := st186_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p229 : ((3236714181087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT186 (i+1))
      = (∑ i ∈ Finset.range 228, stT186 (i+1)) + stT186 229 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 228
    simpa using h
  have hprev := st186_p228
  have hstep := st186_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p230 : ((3340474877267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT186 (i+1))
      = (∑ i ∈ Finset.range 229, stT186 (i+1)) + stT186 230 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 229
    simpa using h
  have hprev := st186_p229
  have hstep := st186_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p231 : ((3186585168083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT186 (i+1))
      = (∑ i ∈ Finset.range 230, stT186 (i+1)) + stT186 231 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 230
    simpa using h
  have hprev := st186_p230
  have hstep := st186_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p232 : ((5742286110877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT186 (i+1))
      = (∑ i ∈ Finset.range 231, stT186 (i+1)) + stT186 232 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 231
    simpa using h
  have hprev := st186_p231
  have hstep := st186_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p233 : ((5173524258283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT186 (i+1))
      = (∑ i ∈ Finset.range 232, stT186 (i+1)) + stT186 233 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 232
    simpa using h
  have hprev := st186_p232
  have hstep := st186_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p234 : ((1252174578487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT186 (i+1))
      = (∑ i ∈ Finset.range 233, stT186 (i+1)) + stT186 234 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 233
    simpa using h
  have hprev := st186_p233
  have hstep := st186_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p235 : ((1335781012017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT186 (i+1))
      = (∑ i ∈ Finset.range 234, stT186 (i+1)) + stT186 235 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 234
    simpa using h
  have hprev := st186_p234
  have hstep := st186_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p236 : ((1493741849569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT186 (i+1))
      = (∑ i ∈ Finset.range 235, stT186 (i+1)) + stT186 236 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 235
    simpa using h
  have hprev := st186_p235
  have hstep := st186_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p237 : ((6530795147179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT186 (i+1))
      = (∑ i ∈ Finset.range 236, stT186 (i+1)) + stT186 237 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 236
    simpa using h
  have hprev := st186_p236
  have hstep := st186_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p238 : ((1337449343933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT186 (i+1))
      = (∑ i ∈ Finset.range 237, stT186 (i+1)) + stT186 238 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 237
    simpa using h
  have hprev := st186_p237
  have hstep := st186_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p239 : ((6356835978371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT186 (i+1))
      = (∑ i ∈ Finset.range 238, stT186 (i+1)) + stT186 239 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 238
    simpa using h
  have hprev := st186_p238
  have hstep := st186_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p240 : ((5732689115717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT186 (i+1))
      = (∑ i ∈ Finset.range 239, stT186 (i+1)) + stT186 240 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 239
    simpa using h
  have hprev := st186_p239
  have hstep := st186_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p241 : ((2586069592609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT186 (i+1))
      = (∑ i ∈ Finset.range 240, stT186 (i+1)) + stT186 241 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 240
    simpa using h
  have hprev := st186_p240
  have hstep := st186_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p242 : ((1247791808567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT186 (i+1))
      = (∑ i ∈ Finset.range 241, stT186 (i+1)) + stT186 242 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 241
    simpa using h
  have hprev := st186_p241
  have hstep := st186_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p243 : ((82629994637/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT186 (i+1))
      = (∑ i ∈ Finset.range 242, stT186 (i+1)) + stT186 243 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 242
    simpa using h
  have hprev := st186_p242
  have hstep := st186_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p244 : ((736863270033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT186 (i+1))
      = (∑ i ∈ Finset.range 243, stT186 (i+1)) + stT186 244 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 243
    simpa using h
  have hprev := st186_p243
  have hstep := st186_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p245 : ((809265489923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT186 (i+1))
      = (∑ i ∈ Finset.range 244, stT186 (i+1)) + stT186 245 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 244
    simpa using h
  have hprev := st186_p244
  have hstep := st186_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p246 : ((209662702471/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT186 (i+1))
      = (∑ i ∈ Finset.range 245, stT186 (i+1)) + stT186 246 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 245
    simpa using h
  have hprev := st186_p245
  have hstep := st186_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p247 : ((3237501984421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT186 (i+1))
      = (∑ i ∈ Finset.range 246, stT186 (i+1)) + stT186 247 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 246
    simpa using h
  have hprev := st186_p246
  have hstep := st186_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p248 : ((5901103400063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT186 (i+1))
      = (∑ i ∈ Finset.range 247, stT186 (i+1)) + stT186 248 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 247
    simpa using h
  have hprev := st186_p247
  have hstep := st186_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p249 : ((5296802251813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT186 (i+1))
      = (∑ i ∈ Finset.range 248, stT186 (i+1)) + stT186 249 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 248
    simpa using h
  have hprev := st186_p248
  have hstep := st186_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p250 : ((996590710257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT186 (i+1))
      = (∑ i ∈ Finset.range 249, stT186 (i+1)) + stT186 250 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 249
    simpa using h
  have hprev := st186_p249
  have hstep := st186_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p251 : ((5122704952437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT186 (i+1))
      = (∑ i ∈ Finset.range 250, stT186 (i+1)) + stT186 251 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 250
    simpa using h
  have hprev := st186_p250
  have hstep := st186_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p252 : ((5639747735577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT186 (i+1))
      = (∑ i ∈ Finset.range 251, stT186 (i+1)) + stT186 252 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 251
    simpa using h
  have hprev := st186_p251
  have hstep := st186_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p253 : ((6263210372803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT186 (i+1))
      = (∑ i ∈ Finset.range 252, stT186 (i+1)) + stT186 253 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 252
    simpa using h
  have hprev := st186_p252
  have hstep := st186_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p254 : ((6671394948503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT186 (i+1))
      = (∑ i ∈ Finset.range 253, stT186 (i+1)) + stT186 254 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 253
    simpa using h
  have hprev := st186_p253
  have hstep := st186_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p255 : ((3328640857839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT186 (i+1))
      = (∑ i ∈ Finset.range 254, stT186 (i+1)) + stT186 255 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 254
    simpa using h
  have hprev := st186_p254
  have hstep := st186_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p256 : ((3115504266821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT186 (i+1))
      = (∑ i ∈ Finset.range 255, stT186 (i+1)) + stT186 256 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 255
    simpa using h
  have hprev := st186_p255
  have hstep := st186_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p257 : ((112200351727/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT186 (i+1))
      = (∑ i ∈ Finset.range 256, stT186 (i+1)) + stT186 257 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 256
    simpa using h
  have hprev := st186_p256
  have hstep := st186_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p258 : ((1276471652327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT186 (i+1))
      = (∑ i ∈ Finset.range 257, stT186 (i+1)) + stT186 258 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 257
    simpa using h
  have hprev := st186_p257
  have hstep := st186_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p259 : ((310485297343/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT186 (i+1))
      = (∑ i ∈ Finset.range 258, stT186 (i+1)) + stT186 259 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 258
    simpa using h
  have hprev := st186_p258
  have hstep := st186_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p260 : ((263052972667/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT186 (i+1))
      = (∑ i ∈ Finset.range 259, stT186 (i+1)) + stT186 260 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 259
    simpa using h
  have hprev := st186_p259
  have hstep := st186_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p261 : ((1459857823529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT186 (i+1))
      = (∑ i ∈ Finset.range 260, stT186 (i+1)) + stT186 261 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 260
    simpa using h
  have hprev := st186_p260
  have hstep := st186_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p262 : ((3210172477249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT186 (i+1))
      = (∑ i ∈ Finset.range 261, stT186 (i+1)) + stT186 262 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 261
    simpa using h
  have hprev := st186_p261
  have hstep := st186_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p263 : ((3362028962269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT186 (i+1))
      = (∑ i ∈ Finset.range 262, stT186 (i+1)) + stT186 263 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 262
    simpa using h
  have hprev := st186_p262
  have hstep := st186_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p264 : ((1651823462059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT186 (i+1))
      = (∑ i ∈ Finset.range 263, stT186 (i+1)) + stT186 264 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 263
    simpa using h
  have hprev := st186_p263
  have hstep := st186_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p265 : ((1532088725089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT186 (i+1))
      = (∑ i ∈ Finset.range 264, stT186 (i+1)) + stT186 265 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 264
    simpa using h
  have hprev := st186_p264
  have hstep := st186_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p266 : ((689419720247/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT186 (i+1))
      = (∑ i ∈ Finset.range 265, stT186 (i+1)) + stT186 266 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 265
    simpa using h
  have hprev := st186_p265
  have hstep := st186_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p267 : ((2527964999183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT186 (i+1))
      = (∑ i ∈ Finset.range 266, stT186 (i+1)) + stT186 267 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 266
    simpa using h
  have hprev := st186_p266
  have hstep := st186_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p268 : ((496235908003/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT186 (i+1))
      = (∑ i ∈ Finset.range 267, stT186 (i+1)) + stT186 268 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 267
    simpa using h
  have hprev := st186_p267
  have hstep := st186_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p269 : ((263763996681/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT186 (i+1))
      = (∑ i ∈ Finset.range 268, stT186 (i+1)) + stT186 269 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 268
    simpa using h
  have hprev := st186_p268
  have hstep := st186_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p270 : ((292433044179/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT186 (i+1))
      = (∑ i ∈ Finset.range 269, stT186 (i+1)) + stT186 270 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 269
    simpa using h
  have hprev := st186_p269
  have hstep := st186_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p271 : ((1605021711463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT186 (i+1))
      = (∑ i ∈ Finset.range 270, stT186 (i+1)) + stT186 271 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 270
    simpa using h
  have hprev := st186_p270
  have hstep := st186_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p272 : ((1346330464397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT186 (i+1))
      = (∑ i ∈ Finset.range 271, stT186 (i+1)) + stT186 272 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 271
    simpa using h
  have hprev := st186_p271
  have hstep := st186_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p273 : ((6645463012961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT186 (i+1))
      = (∑ i ∈ Finset.range 272, stT186 (i+1)) + stT186 273 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 272
    simpa using h
  have hprev := st186_p272
  have hstep := st186_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p274 : ((6202523654099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT186 (i+1))
      = (∑ i ∈ Finset.range 273, stT186 (i+1)) + stT186 274 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 273
    simpa using h
  have hprev := st186_p273
  have hstep := st186_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p275 : ((350059960421/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT186 (i+1))
      = (∑ i ∈ Finset.range 274, stT186 (i+1)) + stT186 275 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 274
    simpa using h
  have hprev := st186_p274
  have hstep := st186_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p276 : ((79778007609/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT186 (i+1))
      = (∑ i ∈ Finset.range 275, stT186 (i+1)) + stT186 276 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 275
    simpa using h
  have hprev := st186_p275
  have hstep := st186_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p277 : ((308255716759/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT186 (i+1))
      = (∑ i ∈ Finset.range 276, stT186 (i+1)) + stT186 277 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 276
    simpa using h
  have hprev := st186_p276
  have hstep := st186_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p278 : ((161027328737/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT186 (i+1))
      = (∑ i ∈ Finset.range 277, stT186 (i+1)) + stT186 278 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 277
    simpa using h
  have hprev := st186_p277
  have hstep := st186_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p279 : ((354414276029/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT186 (i+1))
      = (∑ i ∈ Finset.range 278, stT186 (i+1)) + stT186 279 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 278
    simpa using h
  have hprev := st186_p278
  have hstep := st186_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p280 : ((3131200071/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT186 (i+1))
      = (∑ i ∈ Finset.range 279, stT186 (i+1)) + stT186 280 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 279
    simpa using h
  have hprev := st186_p279
  have hstep := st186_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p281 : ((104325690751/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT186 (i+1))
      = (∑ i ∈ Finset.range 280, stT186 (i+1)) + stT186 281 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 280
    simpa using h
  have hprev := st186_p280
  have hstep := st186_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p282 : ((421289575249/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT186 (i+1))
      = (∑ i ∈ Finset.range 281, stT186 (i+1)) + stT186 282 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 281
    simpa using h
  have hprev := st186_p281
  have hstep := st186_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p283 : ((1607344452579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT186 (i+1))
      = (∑ i ∈ Finset.range 282, stT186 (i+1)) + stT186 283 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 282
    simpa using h
  have hprev := st186_p282
  have hstep := st186_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p284 : ((587476728573/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT186 (i+1))
      = (∑ i ∈ Finset.range 283, stT186 (i+1)) + stT186 284 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 283
    simpa using h
  have hprev := st186_p283
  have hstep := st186_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p285 : ((331696211181/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT186 (i+1))
      = (∑ i ∈ Finset.range 284, stT186 (i+1)) + stT186 285 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 284
    simpa using h
  have hprev := st186_p284
  have hstep := st186_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p286 : ((4959125069311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT186 (i+1))
      = (∑ i ∈ Finset.range 285, stT186 (i+1)) + stT186 286 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 285
    simpa using h
  have hprev := st186_p285
  have hstep := st186_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p287 : ((2485455605019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT186 (i+1))
      = (∑ i ∈ Finset.range 286, stT186 (i+1)) + stT186 287 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 286
    simpa using h
  have hprev := st186_p286
  have hstep := st186_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p288 : ((5335396658053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT186 (i+1))
      = (∑ i ∈ Finset.range 287, stT186 (i+1)) + stT186 288 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 287
    simpa using h
  have hprev := st186_p287
  have hstep := st186_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p289 : ((5903964609063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT186 (i+1))
      = (∑ i ∈ Finset.range 288, stT186 (i+1)) + stT186 289 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 288
    simpa using h
  have hprev := st186_p288
  have hstep := st186_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p290 : ((6448526599383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT186 (i+1))
      = (∑ i ∈ Finset.range 289, stT186 (i+1)) + stT186 290 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 289
    simpa using h
  have hprev := st186_p289
  have hstep := st186_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p291 : ((6753475386223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT186 (i+1))
      = (∑ i ∈ Finset.range 290, stT186 (i+1)) + stT186 291 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 290
    simpa using h
  have hprev := st186_p290
  have hstep := st186_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p292 : ((1340059777483/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT186 (i+1))
      = (∑ i ∈ Finset.range 291, stT186 (i+1)) + stT186 292 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 291
    simpa using h
  have hprev := st186_p291
  have hstep := st186_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p293 : ((6312057115081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT186 (i+1))
      = (∑ i ∈ Finset.range 292, stT186 (i+1)) + stT186 293 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 292
    simpa using h
  have hprev := st186_p292
  have hstep := st186_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p294 : ((5741657116297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT186 (i+1))
      = (∑ i ∈ Finset.range 293, stT186 (i+1)) + stT186 294 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 293
    simpa using h
  have hprev := st186_p293
  have hstep := st186_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p295 : ((104206536219/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT186 (i+1))
      = (∑ i ∈ Finset.range 294, stT186 (i+1)) + stT186 295 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 294
    simpa using h
  have hprev := st186_p294
  have hstep := st186_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p296 : ((4921487646007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT186 (i+1))
      = (∑ i ∈ Finset.range 295, stT186 (i+1)) + stT186 296 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 295
    simpa using h
  have hprev := st186_p295
  have hstep := st186_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p297 : ((4983608906971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT186 (i+1))
      = (∑ i ∈ Finset.range 296, stT186 (i+1)) + stT186 297 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 296
    simpa using h
  have hprev := st186_p296
  have hstep := st186_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p298 : ((5370971483499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT186 (i+1))
      = (∑ i ∈ Finset.range 297, stT186 (i+1)) + stT186 298 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 297
    simpa using h
  have hprev := st186_p297
  have hstep := st186_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p299 : ((5935921803587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT186 (i+1))
      = (∑ i ∈ Finset.range 298, stT186 (i+1)) + stT186 299 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 298
    simpa using h
  have hprev := st186_p298
  have hstep := st186_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p300 : ((6466337867387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT186 (i+1))
      = (∑ i ∈ Finset.range 299, stT186 (i+1)) + stT186 300 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 299
    simpa using h
  have hprev := st186_p299
  have hstep := st186_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p301 : ((6765589180367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT186 (i+1))
      = (∑ i ∈ Finset.range 300, stT186 (i+1)) + stT186 301 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 300
    simpa using h
  have hprev := st186_p300
  have hstep := st186_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p302 : ((6724754515499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT186 (i+1))
      = (∑ i ∈ Finset.range 301, stT186 (i+1)) + stT186 302 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 301
    simpa using h
  have hprev := st186_p301
  have hstep := st186_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p303 : ((6360886057229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT186 (i+1))
      = (∑ i ∈ Finset.range 302, stT186 (i+1)) + stT186 303 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 302
    simpa using h
  have hprev := st186_p302
  have hstep := st186_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p304 : ((5808417343289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT186 (i+1))
      = (∑ i ∈ Finset.range 303, stT186 (i+1)) + stT186 304 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 303
    simpa using h
  have hprev := st186_p303
  have hstep := st186_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p305 : ((1317081626579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT186 (i+1))
      = (∑ i ∈ Finset.range 304, stT186 (i+1)) + stT186 305 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 304
    simpa using h
  have hprev := st186_p304
  have hstep := st186_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p306 : ((2467324555951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT186 (i+1))
      = (∑ i ∈ Finset.range 305, stT186 (i+1)) + stT186 306 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 305
    simpa using h
  have hprev := st186_p305
  have hstep := st186_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p307 : ((4925278279613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT186 (i+1))
      = (∑ i ∈ Finset.range 306, stT186 (i+1)) + stT186 307 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 306
    simpa using h
  have hprev := st186_p306
  have hstep := st186_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p308 : ((1048311199309/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT186 (i+1))
      = (∑ i ∈ Finset.range 307, stT186 (i+1)) + stT186 308 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 307
    simpa using h
  have hprev := st186_p307
  have hstep := st186_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p309 : ((230798316361/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT186 (i+1))
      = (∑ i ∈ Finset.range 308, stT186 (i+1)) + stT186 309 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 308
    simpa using h
  have hprev := st186_p308
  have hstep := st186_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p310 : ((1581000824141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT186 (i+1))
      = (∑ i ∈ Finset.range 309, stT186 (i+1)) + stT186 310 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 309
    simpa using h
  have hprev := st186_p309
  have hstep := st186_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p311 : ((3355280185279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT186 (i+1))
      = (∑ i ∈ Finset.range 310, stT186 (i+1)) + stT186 311 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 310
    simpa using h
  have hprev := st186_p310
  have hstep := st186_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p312 : ((1699211507319/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT186 (i+1))
      = (∑ i ∈ Finset.range 311, stT186 (i+1)) + stT186 312 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 311
    simpa using h
  have hprev := st186_p311
  have hstep := st186_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p313 : ((3277483569679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT186 (i+1))
      = (∑ i ∈ Finset.range 312, stT186 (i+1)) + stT186 313 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 312
    simpa using h
  have hprev := st186_p312
  have hstep := st186_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p314 : ((3034780876369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT186 (i+1))
      = (∑ i ∈ Finset.range 313, stT186 (i+1)) + stT186 314 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 313
    simpa using h
  have hprev := st186_p313
  have hstep := st186_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p315 : ((1376745575963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT186 (i+1))
      = (∑ i ∈ Finset.range 314, stT186 (i+1)) + stT186 315 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 314
    simpa using h
  have hprev := st186_p314
  have hstep := st186_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p316 : ((252881726631/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT186 (i+1))
      = (∑ i ∈ Finset.range 315, stT186 (i+1)) + stT186 316 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 315
    simpa using h
  have hprev := st186_p315
  have hstep := st186_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p317 : ((1217905060909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT186 (i+1))
      = (∑ i ∈ Finset.range 316, stT186 (i+1)) + stT186 317 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 316
    simpa using h
  have hprev := st186_p316
  have hstep := st186_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p318 : ((626176712531/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT186 (i+1))
      = (∑ i ∈ Finset.range 317, stT186 (i+1)) + stT186 318 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 317
    simpa using h
  have hprev := st186_p317
  have hstep := st186_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p319 : ((1355855480101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT186 (i+1))
      = (∑ i ∈ Finset.range 318, stT186 (i+1)) + stT186 319 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 318
    simpa using h
  have hprev := st186_p318
  have hstep := st186_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p320 : ((1493898052617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT186 (i+1))
      = (∑ i ∈ Finset.range 319, stT186 (i+1)) + stT186 320 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 319
    simpa using h
  have hprev := st186_p319
  have hstep := st186_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p321 : ((1621070274577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT186 (i+1))
      = (∑ i ∈ Finset.range 320, stT186 (i+1)) + stT186 321 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 320
    simpa using h
  have hprev := st186_p320
  have hstep := st186_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p322 : ((1696038097527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT186 (i+1))
      = (∑ i ∈ Finset.range 321, stT186 (i+1)) + stT186 322 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 321
    simpa using h
  have hprev := st186_p321
  have hstep := st186_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p323 : ((3389695295269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT186 (i+1))
      = (∑ i ∈ Finset.range 322, stT186 (i+1)) + stT186 323 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 322
    simpa using h
  have hprev := st186_p322
  have hstep := st186_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p324 : ((3236646839497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT186 (i+1))
      = (∑ i ∈ Finset.range 323, stT186 (i+1)) + stT186 324 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 323
    simpa using h
  have hprev := st186_p323
  have hstep := st186_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p325 : ((1491364841621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT186 (i+1))
      = (∑ i ∈ Finset.range 324, stT186 (i+1)) + stT186 325 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 324
    simpa using h
  have hprev := st186_p324
  have hstep := st186_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p326 : ((5418418832241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT186 (i+1))
      = (∑ i ∈ Finset.range 325, stT186 (i+1)) + stT186 326 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 325
    simpa using h
  have hprev := st186_p325
  have hstep := st186_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p327 : ((5005190299749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT186 (i+1))
      = (∑ i ∈ Finset.range 326, stT186 (i+1)) + stT186 327 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 326
    simpa using h
  have hprev := st186_p326
  have hstep := st186_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p328 : ((4854757061281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT186 (i+1))
      = (∑ i ∈ Finset.range 327, stT186 (i+1)) + stT186 328 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 327
    simpa using h
  have hprev := st186_p327
  have hstep := st186_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p329 : ((2506274474267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT186 (i+1))
      = (∑ i ∈ Finset.range 328, stT186 (i+1)) + stT186 329 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 328
    simpa using h
  have hprev := st186_p328
  have hstep := st186_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p330 : ((5427830163491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT186 (i+1))
      = (∑ i ∈ Finset.range 329, stT186 (i+1)) + stT186 330 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 329
    simpa using h
  have hprev := st186_p329
  have hstep := st186_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p331 : ((93297088161/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT186 (i+1))
      = (∑ i ∈ Finset.range 330, stT186 (i+1)) + stT186 331 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 330
    simpa using h
  have hprev := st186_p330
  have hstep := st186_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p332 : ((6474783572877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT186 (i+1))
      = (∑ i ∈ Finset.range 331, stT186 (i+1)) + stT186 332 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 331
    simpa using h
  have hprev := st186_p331
  have hstep := st186_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p333 : ((1357153493381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT186 (i+1))
      = (∑ i ∈ Finset.range 332, stT186 (i+1)) + stT186 333 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 332
    simpa using h
  have hprev := st186_p332
  have hstep := st186_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p334 : ((1362158174801/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT186 (i+1))
      = (∑ i ∈ Finset.range 333, stT186 (i+1)) + stT186 334 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 333
    simpa using h
  have hprev := st186_p333
  have hstep := st186_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p335 : ((3271957905253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT186 (i+1))
      = (∑ i ∈ Finset.range 334, stT186 (i+1)) + stT186 335 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 334
    simpa using h
  have hprev := st186_p334
  have hstep := st186_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p336 : ((758342722897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT186 (i+1))
      = (∑ i ∈ Finset.range 335, stT186 (i+1)) + stT186 336 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 335
    simpa using h
  have hprev := st186_p335
  have hstep := st186_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p337 : ((1380642782159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT186 (i+1))
      = (∑ i ∈ Finset.range 336, stT186 (i+1)) + stT186 337 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 336
    simpa using h
  have hprev := st186_p336
  have hstep := st186_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p338 : ((1268230063587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT186 (i+1))
      = (∑ i ∈ Finset.range 337, stT186 (i+1)) + stT186 338 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 337
    simpa using h
  have hprev := st186_p337
  have hstep := st186_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p339 : ((1212413547693/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT186 (i+1))
      = (∑ i ∈ Finset.range 338, stT186 (i+1)) + stT186 339 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 338
    simpa using h
  have hprev := st186_p338
  have hstep := st186_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p340 : ((307303498421/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT186 (i+1))
      = (∑ i ∈ Finset.range 339, stT186 (i+1)) + stT186 340 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 339
    simpa using h
  have hprev := st186_p339
  have hstep := st186_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p341 : ((1313333910059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT186 (i+1))
      = (∑ i ∈ Finset.range 340, stT186 (i+1)) + stT186 341 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 340
    simpa using h
  have hprev := st186_p340
  have hstep := st186_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p342 : ((2880108205921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT186 (i+1))
      = (∑ i ∈ Finset.range 341, stT186 (i+1)) + stT186 342 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 341
    simpa using h
  have hprev := st186_p341
  have hstep := st186_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p343 : ((6290679047861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT186 (i+1))
      = (∑ i ∈ Finset.range 342, stT186 (i+1)) + stT186 343 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 342
    simpa using h
  have hprev := st186_p342
  have hstep := st186_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p344 : ((267712076393/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT186 (i+1))
      = (∑ i ∈ Finset.range 343, stT186 (i+1)) + stT186 344 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 343
    simpa using h
  have hprev := st186_p343
  have hstep := st186_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p345 : ((171321766421/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT186 (i+1))
      = (∑ i ∈ Finset.range 344, stT186 (i+1)) + stT186 345 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 344
    simpa using h
  have hprev := st186_p344
  have hstep := st186_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p346 : ((420433154287/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT186 (i+1))
      = (∑ i ∈ Finset.range 345, stT186 (i+1)) + stT186 346 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 345
    simpa using h
  have hprev := st186_p345
  have hstep := st186_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p347 : ((3175982537507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT186 (i+1))
      = (∑ i ∈ Finset.range 346, stT186 (i+1)) + stT186 347 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 346
    simpa using h
  have hprev := st186_p346
  have hstep := st186_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p348 : ((2917110963181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT186 (i+1))
      = (∑ i ∈ Finset.range 347, stT186 (i+1)) + stT186 348 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 347
    simpa using h
  have hprev := st186_p347
  have hstep := st186_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p349 : ((2659249351381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT186 (i+1))
      = (∑ i ∈ Finset.range 348, stT186 (i+1)) + stT186 349 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 348
    simpa using h
  have hprev := st186_p348
  have hstep := st186_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p350 : ((4947437646869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT186 (i+1))
      = (∑ i ∈ Finset.range 349, stT186 (i+1)) + stT186 350 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 349
    simpa using h
  have hprev := st186_p349
  have hstep := st186_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p351 : ((4822324068469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT186 (i+1))
      = (∑ i ∈ Finset.range 350, stT186 (i+1)) + stT186 351 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 350
    simpa using h
  have hprev := st186_p350
  have hstep := st186_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p352 : ((622004861483/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT186 (i+1))
      = (∑ i ∈ Finset.range 351, stT186 (i+1)) + stT186 352 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 351
    simpa using h
  have hprev := st186_p351
  have hstep := st186_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p353 : ((2682629075003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT186 (i+1))
      = (∑ i ∈ Finset.range 352, stT186 (i+1)) + stT186 353 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 352
    simpa using h
  have hprev := st186_p352
  have hstep := st186_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p354 : ((2941702636339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT186 (i+1))
      = (∑ i ∈ Finset.range 353, stT186 (i+1)) + stT186 354 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 353
    simpa using h
  have hprev := st186_p353
  have hstep := st186_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p355 : ((3195184378507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT186 (i+1))
      = (∑ i ∈ Finset.range 354, stT186 (i+1)) + stT186 355 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 354
    simpa using h
  have hprev := st186_p354
  have hstep := st186_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p356 : ((1687636861961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT186 (i+1))
      = (∑ i ∈ Finset.range 355, stT186 (i+1)) + stT186 356 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 355
    simpa using h
  have hprev := st186_p355
  have hstep := st186_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p357 : ((1717219361453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT186 (i+1))
      = (∑ i ∈ Finset.range 356, stT186 (i+1)) + stT186 357 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 356
    simpa using h
  have hprev := st186_p356
  have hstep := st186_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p358 : ((6715319474047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT186 (i+1))
      = (∑ i ∈ Finset.range 357, stT186 (i+1)) + stT186 358 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 357
    simpa using h
  have hprev := st186_p357
  have hstep := st186_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p359 : ((6331731081167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT186 (i+1))
      = (∑ i ∈ Finset.range 358, stT186 (i+1)) + stT186 359 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 358
    simpa using h
  have hprev := st186_p358
  have hstep := st186_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p360 : ((1454935585251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT186 (i+1))
      = (∑ i ∈ Finset.range 359, stT186 (i+1)) + stT186 360 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 359
    simpa using h
  have hprev := st186_p359
  have hstep := st186_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p361 : ((664167043621/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT186 (i+1))
      = (∑ i ∈ Finset.range 360, stT186 (i+1)) + stT186 361 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 360
    simpa using h
  have hprev := st186_p360
  have hstep := st186_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p362 : ((2471809588171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT186 (i+1))
      = (∑ i ∈ Finset.range 361, stT186 (i+1)) + stT186 362 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 361
    simpa using h
  have hprev := st186_p361
  have hstep := st186_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p363 : ((2402544598251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT186 (i+1))
      = (∑ i ∈ Finset.range 362, stT186 (i+1)) + stT186 363 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 362
    simpa using h
  have hprev := st186_p362
  have hstep := st186_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p364 : ((2466006663327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT186 (i+1))
      = (∑ i ∈ Finset.range 363, stT186 (i+1)) + stT186 364 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 363
    simpa using h
  have hprev := st186_p363
  have hstep := st186_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p365 : ((1058131192351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT186 (i+1))
      = (∑ i ∈ Finset.range 364, stT186 (i+1)) + stT186 365 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 364
    simpa using h
  have hprev := st186_p364
  have hstep := st186_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p366 : ((5788902795479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT186 (i+1))
      = (∑ i ∈ Finset.range 365, stT186 (i+1)) + stT186 366 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 365
    simpa using h
  have hprev := st186_p365
  have hstep := st186_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p367 : ((1575102859481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT186 (i+1))
      = (∑ i ∈ Finset.range 366, stT186 (i+1)) + stT186 367 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 366
    simpa using h
  have hprev := st186_p366
  have hstep := st186_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p368 : ((1674210796373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT186 (i+1))
      = (∑ i ∈ Finset.range 367, stT186 (i+1)) + stT186 368 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 367
    simpa using h
  have hprev := st186_p367
  have hstep := st186_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p369 : ((1719976978579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT186 (i+1))
      = (∑ i ∈ Finset.range 368, stT186 (i+1)) + stT186 369 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 368
    simpa using h
  have hprev := st186_p368
  have hstep := st186_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p370 : ((1701319928629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT186 (i+1))
      = (∑ i ∈ Finset.range 369, stT186 (i+1)) + stT186 370 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 369
    simpa using h
  have hprev := st186_p369
  have hstep := st186_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p371 : ((1623176822679/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT186 (i+1))
      = (∑ i ∈ Finset.range 370, stT186 (i+1)) + stT186 371 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 370
    simpa using h
  have hprev := st186_p370
  have hstep := st186_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p372 : ((752517468517/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT186 (i+1))
      = (∑ i ∈ Finset.range 371, stT186 (i+1)) + stT186 372 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 371
    simpa using h
  have hprev := st186_p371
  have hstep := st186_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p373 : ((2751898571877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT186 (i+1))
      = (∑ i ∈ Finset.range 372, stT186 (i+1)) + stT186 373 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 372
    simpa using h
  have hprev := st186_p372
  have hstep := st186_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p374 : ((506933049857/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT186 (i+1))
      = (∑ i ∈ Finset.range 373, stT186 (i+1)) + stT186 374 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 373
    simpa using h
  have hprev := st186_p373
  have hstep := st186_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p375 : ((482131486713/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT186 (i+1))
      = (∑ i ∈ Finset.range 374, stT186 (i+1)) + stT186 375 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 374
    simpa using h
  have hprev := st186_p374
  have hstep := st186_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p376 : ((4818410898489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT186 (i+1))
      = (∑ i ∈ Finset.range 375, stT186 (i+1)) + stT186 376 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 375
    simpa using h
  have hprev := st186_p375
  have hstep := st186_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p377 : ((5060058522559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT186 (i+1))
      = (∑ i ∈ Finset.range 376, stT186 (i+1)) + stT186 377 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 376
    simpa using h
  have hprev := st186_p376
  have hstep := st186_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p378 : ((5487523134487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT186 (i+1))
      = (∑ i ∈ Finset.range 377, stT186 (i+1)) + stT186 378 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 377
    simpa using h
  have hprev := st186_p377
  have hstep := st186_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p379 : ((2999343549801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT186 (i+1))
      = (∑ i ∈ Finset.range 378, stT186 (i+1)) + stT186 379 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 378
    simpa using h
  have hprev := st186_p378
  have hstep := st186_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p380 : ((1294551843019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT186 (i+1))
      = (∑ i ∈ Finset.range 379, stT186 (i+1)) + stT186 380 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 379
    simpa using h
  have hprev := st186_p379
  have hstep := st186_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p381 : ((1359774255817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT186 (i+1))
      = (∑ i ∈ Finset.range 380, stT186 (i+1)) + stT186 381 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 380
    simpa using h
  have hprev := st186_p380
  have hstep := st186_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p382 : ((6901754189537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT186 (i+1))
      = (∑ i ∈ Finset.range 381, stT186 (i+1)) + stT186 382 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 381
    simpa using h
  have hprev := st186_p381
  have hstep := st186_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p383 : ((3379339548303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT186 (i+1))
      = (∑ i ∈ Finset.range 382, stT186 (i+1)) + stT186 383 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 382
    simpa using h
  have hprev := st186_p382
  have hstep := st186_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p384 : ((1600965730043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT186 (i+1))
      = (∑ i ∈ Finset.range 383, stT186 (i+1)) + stT186 384 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 383
    simpa using h
  have hprev := st186_p383
  have hstep := st186_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p385 : ((1479947009379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT186 (i+1))
      = (∑ i ∈ Finset.range 384, stT186 (i+1)) + stT186 385 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 384
    simpa using h
  have hprev := st186_p384
  have hstep := st186_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p386 : ((1354405365829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT186 (i+1))
      = (∑ i ∈ Finset.range 385, stT186 (i+1)) + stT186 386 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 385
    simpa using h
  have hprev := st186_p385
  have hstep := st186_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p387 : ((1002304603367/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT186 (i+1))
      = (∑ i ∈ Finset.range 386, stT186 (i+1)) + stT186 387 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 386
    simpa using h
  have hprev := st186_p386
  have hstep := st186_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p388 : ((4792803858111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT186 (i+1))
      = (∑ i ∈ Finset.range 387, stT186 (i+1)) + stT186 388 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 387
    simpa using h
  have hprev := st186_p387
  have hstep := st186_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p389 : ((4809715510211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT186 (i+1))
      = (∑ i ∈ Finset.range 388, stT186 (i+1)) + stT186 389 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 388
    simpa using h
  have hprev := st186_p388
  have hstep := st186_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p390 : ((5057306658237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT186 (i+1))
      = (∑ i ∈ Finset.range 389, stT186 (i+1)) + stT186 390 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 389
    simpa using h
  have hprev := st186_p389
  have hstep := st186_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p391 : ((684914267993/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT186 (i+1))
      = (∑ i ∈ Finset.range 390, stT186 (i+1)) + stT186 391 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 390
    simpa using h
  have hprev := st186_p390
  have hstep := st186_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p392 : ((149534951843/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT186 (i+1))
      = (∑ i ∈ Finset.range 391, stT186 (i+1)) + stT186 392 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 391
    simpa using h
  have hprev := st186_p391
  have hstep := st186_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p393 : ((6452494610049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT186 (i+1))
      = (∑ i ∈ Finset.range 392, stT186 (i+1)) + stT186 393 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 392
    simpa using h
  have hprev := st186_p392
  have hstep := st186_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p394 : ((6789431707233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT186 (i+1))
      = (∑ i ∈ Finset.range 393, stT186 (i+1)) + stT186 394 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 393
    simpa using h
  have hprev := st186_p393
  have hstep := st186_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p395 : ((6919336510107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT186 (i+1))
      = (∑ i ∈ Finset.range 394, stT186 (i+1)) + stT186 395 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 394
    simpa using h
  have hprev := st186_p394
  have hstep := st186_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p396 : ((3407496983733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT186 (i+1))
      = (∑ i ∈ Finset.range 395, stT186 (i+1)) + stT186 396 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 395
    simpa using h
  have hprev := st186_p395
  have hstep := st186_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p397 : ((3250044304041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT186 (i+1))
      = (∑ i ∈ Finset.range 396, stT186 (i+1)) + stT186 397 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 396
    simpa using h
  have hprev := st186_p396
  have hstep := st186_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p398 : ((6043329513177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT186 (i+1))
      = (∑ i ∈ Finset.range 397, stT186 (i+1)) + stT186 398 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 397
    simpa using h
  have hprev := st186_p397
  have hstep := st186_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p399 : ((5543121037349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT186 (i+1))
      = (∑ i ∈ Finset.range 398, stT186 (i+1)) + stT186 399 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 398
    simpa using h
  have hprev := st186_p398
  have hstep := st186_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p400 : ((5106155163419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT186 (i+1))
      = (∑ i ∈ Finset.range 399, stT186 (i+1)) + stT186 400 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 399
    simpa using h
  have hprev := st186_p399
  have hstep := st186_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p401 : ((192987811997/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT186 (i+1))
      = (∑ i ∈ Finset.range 400, stT186 (i+1)) + stT186 401 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 400
    simpa using h
  have hprev := st186_p400
  have hstep := st186_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p402 : ((951463896897/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT186 (i+1))
      = (∑ i ∈ Finset.range 401, stT186 (i+1)) + stT186 402 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 401
    simpa using h
  have hprev := st186_p401
  have hstep := st186_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p403 : ((983427825069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT186 (i+1))
      = (∑ i ∈ Finset.range 402, stT186 (i+1)) + stT186 403 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 402
    simpa using h
  have hprev := st186_p402
  have hstep := st186_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p404 : ((5269696300721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT186 (i+1))
      = (∑ i ∈ Finset.range 403, stT186 (i+1)) + stT186 404 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 403
    simpa using h
  have hprev := st186_p403
  have hstep := st186_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p405 : ((5740824942111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT186 (i+1))
      = (∑ i ∈ Finset.range 404, stT186 (i+1)) + stT186 405 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 404
    simpa using h
  have hprev := st186_p404
  have hstep := st186_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p406 : ((779068944223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT186 (i+1))
      = (∑ i ∈ Finset.range 405, stT186 (i+1)) + stT186 406 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 405
    simpa using h
  have hprev := st186_p405
  have hstep := st186_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p407 : ((6643602458249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT186 (i+1))
      = (∑ i ∈ Finset.range 406, stT186 (i+1)) + stT186 407 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 406
    simpa using h
  have hprev := st186_p406
  have hstep := st186_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p408 : ((6890186437797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT186 (i+1))
      = (∑ i ∈ Finset.range 407, stT186 (i+1)) + stT186 408 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 407
    simpa using h
  have hprev := st186_p407
  have hstep := st186_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p409 : ((6922826270477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT186 (i+1))
      = (∑ i ∈ Finset.range 408, stT186 (i+1)) + stT186 409 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 408
    simpa using h
  have hprev := st186_p408
  have hstep := st186_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p410 : ((6735906269817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT186 (i+1))
      = (∑ i ∈ Finset.range 409, stT186 (i+1)) + stT186 410 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 409
    simpa using h
  have hprev := st186_p409
  have hstep := st186_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p411 : ((6368174998233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT186 (i+1))
      = (∑ i ∈ Finset.range 410, stT186 (i+1)) + stT186 411 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 410
    simpa using h
  have hprev := st186_p410
  have hstep := st186_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p412 : ((5894343595853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT186 (i+1))
      = (∑ i ∈ Finset.range 411, stT186 (i+1)) + stT186 412 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 411
    simpa using h
  have hprev := st186_p411
  have hstep := st186_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p413 : ((5409623647297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT186 (i+1))
      = (∑ i ∈ Finset.range 412, stT186 (i+1)) + stT186 413 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 412
    simpa using h
  have hprev := st186_p412
  have hstep := st186_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p414 : ((1002099718969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT186 (i+1))
      = (∑ i ∈ Finset.range 413, stT186 (i+1)) + stT186 414 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 413
    simpa using h
  have hprev := st186_p413
  have hstep := st186_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p415 : ((596950461421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT186 (i+1))
      = (∑ i ∈ Finset.range 414, stT186 (i+1)) + stT186 415 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 414
    simpa using h
  have hprev := st186_p414
  have hstep := st186_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p416 : ((2375228332989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT186 (i+1))
      = (∑ i ∈ Finset.range 415, stT186 (i+1)) + stT186 416 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 415
    simpa using h
  have hprev := st186_p415
  have hstep := st186_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p417 : ((154344370281/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT186 (i+1))
      = (∑ i ∈ Finset.range 416, stT186 (i+1)) + stT186 417 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 416
    simpa using h
  have hprev := st186_p416
  have hstep := st186_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p418 : ((1325870728253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT186 (i+1))
      = (∑ i ∈ Finset.range 417, stT186 (i+1)) + stT186 418 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 417
    simpa using h
  have hprev := st186_p417
  have hstep := st186_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p419 : ((2886105898729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT186 (i+1))
      = (∑ i ∈ Finset.range 418, stT186 (i+1)) + stT186 419 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 418
    simpa using h
  have hprev := st186_p418
  have hstep := st186_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p420 : ((1563517435427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT186 (i+1))
      = (∑ i ∈ Finset.range 419, stT186 (i+1)) + stT186 420 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 419
    simpa using h
  have hprev := st186_p419
  have hstep := st186_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p421 : ((3328117640729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT186 (i+1))
      = (∑ i ∈ Finset.range 420, stT186 (i+1)) + stT186 421 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 420
    simpa using h
  have hprev := st186_p420
  have hstep := st186_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p422 : ((3451006577357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT186 (i+1))
      = (∑ i ∈ Finset.range 421, stT186 (i+1)) + stT186 422 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 421
    simpa using h
  have hprev := st186_p421
  have hstep := st186_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p423 : ((3472624713149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT186 (i+1))
      = (∑ i ∈ Finset.range 422, stT186 (i+1)) + stT186 423 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 422
    simpa using h
  have hprev := st186_p422
  have hstep := st186_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p424 : ((3389324311931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT186 (i+1))
      = (∑ i ∈ Finset.range 423, stT186 (i+1)) + stT186 424 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 423
    simpa using h
  have hprev := st186_p423
  have hstep := st186_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p425 : ((3217321418771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT186 (i+1))
      = (∑ i ∈ Finset.range 424, stT186 (i+1)) + stT186 425 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 424
    simpa using h
  have hprev := st186_p424
  have hstep := st186_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p426 : ((2989364681277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT186 (i+1))
      = (∑ i ∈ Finset.range 425, stT186 (i+1)) + stT186 426 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 425
    simpa using h
  have hprev := st186_p425
  have hstep := st186_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p427 : ((1374190396599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT186 (i+1))
      = (∑ i ∈ Finset.range 426, stT186 (i+1)) + stT186 427 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 426
    simpa using h
  have hprev := st186_p426
  have hstep := st186_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p428 : ((507865996899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT186 (i+1))
      = (∑ i ∈ Finset.range 427, stT186 (i+1)) + stT186 428 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 427
    simpa using h
  have hprev := st186_p427
  have hstep := st186_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p429 : ((480169212147/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT186 (i+1))
      = (∑ i ∈ Finset.range 428, stT186 (i+1)) + stT186 429 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 428
    simpa using h
  have hprev := st186_p428
  have hstep := st186_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p430 : ((4716353917947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT186 (i+1))
      = (∑ i ∈ Finset.range 429, stT186 (i+1)) + stT186 430 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 429
    simpa using h
  have hprev := st186_p429
  have hstep := st186_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p431 : ((302341015587/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT186 (i+1))
      = (∑ i ∈ Finset.range 430, stT186 (i+1)) + stT186 431 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 430
    simpa using h
  have hprev := st186_p430
  have hstep := st186_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p432 : ((5141919366267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT186 (i+1))
      = (∑ i ∈ Finset.range 431, stT186 (i+1)) + stT186 432 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 431
    simpa using h
  have hprev := st186_p431
  have hstep := st186_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p433 : ((1393367702209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT186 (i+1))
      = (∑ i ∈ Finset.range 432, stT186 (i+1)) + stT186 433 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 432
    simpa using h
  have hprev := st186_p432
  have hstep := st186_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p434 : ((6053294282851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT186 (i+1))
      = (∑ i ∈ Finset.range 433, stT186 (i+1)) + stT186 434 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 433
    simpa using h
  have hprev := st186_p433
  have hstep := st186_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p435 : ((3247286664497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT186 (i+1))
      = (∑ i ∈ Finset.range 434, stT186 (i+1)) + stT186 435 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 434
    simpa using h
  have hprev := st186_p434
  have hstep := st186_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p436 : ((6818194478527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT186 (i+1))
      = (∑ i ∈ Finset.range 435, stT186 (i+1)) + stT186 436 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 435
    simpa using h
  have hprev := st186_p435
  have hstep := st186_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p437 : ((6966798733491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT186 (i+1))
      = (∑ i ∈ Finset.range 436, stT186 (i+1)) + stT186 437 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 436
    simpa using h
  have hprev := st186_p436
  have hstep := st186_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p438 : ((1728671828883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT186 (i+1))
      = (∑ i ∈ Finset.range 437, stT186 (i+1)) + stT186 438 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 437
    simpa using h
  have hprev := st186_p437
  have hstep := st186_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p439 : ((3335993163711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT186 (i+1))
      = (∑ i ∈ Finset.range 438, stT186 (i+1)) + stT186 439 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 438
    simpa using h
  have hprev := st186_p438
  have hstep := st186_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p440 : ((628235755441/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT186 (i+1))
      = (∑ i ∈ Finset.range 439, stT186 (i+1)) + stT186 440 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 439
    simpa using h
  have hprev := st186_p439
  have hstep := st186_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p441 : ((2907444234383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT186 (i+1))
      = (∑ i ∈ Finset.range 440, stT186 (i+1)) + stT186 441 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 440
    simpa using h
  have hprev := st186_p440
  have hstep := st186_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p442 : ((2675833341241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT186 (i+1))
      = (∑ i ∈ Finset.range 441, stT186 (i+1)) + stT186 442 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 441
    simpa using h
  have hprev := st186_p441
  have hstep := st186_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p443 : ((4973319779877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT186 (i+1))
      = (∑ i ∈ Finset.range 442, stT186 (i+1)) + stT186 443 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 442
    simpa using h
  have hprev := st186_p442
  have hstep := st186_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p444 : ((1186263362601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT186 (i+1))
      = (∑ i ∈ Finset.range 443, stT186 (i+1)) + stT186 444 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 443
    simpa using h
  have hprev := st186_p443
  have hstep := st186_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p445 : ((2352798589843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT186 (i+1))
      = (∑ i ∈ Finset.range 444, stT186 (i+1)) + stT186 445 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 444
    simpa using h
  have hprev := st186_p444
  have hstep := st186_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p446 : ((4860908023147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT186 (i+1))
      = (∑ i ∈ Finset.range 445, stT186 (i+1)) + stT186 446 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 445
    simpa using h
  have hprev := st186_p445
  have hstep := st186_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p447 : ((1295891300293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT186 (i+1))
      = (∑ i ∈ Finset.range 446, stT186 (i+1)) + stT186 447 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 446
    simpa using h
  have hprev := st186_p446
  have hstep := st186_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p448 : ((1404474688033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT186 (i+1))
      = (∑ i ∈ Finset.range 447, stT186 (i+1)) + stT186 448 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 447
    simpa using h
  have hprev := st186_p447
  have hstep := st186_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p449 : ((1522444667879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT186 (i+1))
      = (∑ i ∈ Finset.range 448, stT186 (i+1)) + stT186 449 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 448
    simpa using h
  have hprev := st186_p448
  have hstep := st186_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p450 : ((407461602241/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT186 (i+1))
      = (∑ i ∈ Finset.range 449, stT186 (i+1)) + stT186 450 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 449
    simpa using h
  have hprev := st186_p449
  have hstep := st186_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p451 : ((6834693674909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT186 (i+1))
      = (∑ i ∈ Finset.range 450, stT186 (i+1)) + stT186 451 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 450
    simpa using h
  have hprev := st186_p450
  have hstep := st186_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p452 : ((6983434206629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT186 (i+1))
      = (∑ i ∈ Finset.range 451, stT186 (i+1)) + stT186 452 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 451
    simpa using h
  have hprev := st186_p451
  have hstep := st186_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p453 : ((6941529087839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT186 (i+1))
      = (∑ i ∈ Finset.range 452, stT186 (i+1)) + stT186 453 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 452
    simpa using h
  have hprev := st186_p452
  have hstep := st186_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p454 : ((6716751989927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT186 (i+1))
      = (∑ i ∈ Finset.range 453, stT186 (i+1)) + stT186 454 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 453
    simpa using h
  have hprev := st186_p453
  have hstep := st186_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p455 : ((6346993275359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT186 (i+1))
      = (∑ i ∈ Finset.range 454, stT186 (i+1)) + stT186 455 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 454
    simpa using h
  have hprev := st186_p454
  have hstep := st186_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p456 : ((117873591271/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT186 (i+1))
      = (∑ i ∈ Finset.range 455, stT186 (i+1)) + stT186 456 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 455
    simpa using h
  have hprev := st186_p455
  have hstep := st186_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p457 : ((5431384231337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT186 (i+1))
      = (∑ i ∈ Finset.range 456, stT186 (i+1)) + stT186 457 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 456
    simpa using h
  have hprev := st186_p456
  have hstep := st186_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p458 : ((5035509349177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT186 (i+1))
      = (∑ i ∈ Finset.range 457, stT186 (i+1)) + stT186 458 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 457
    simpa using h
  have hprev := st186_p457
  have hstep := st186_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p459 : ((74531837971/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT186 (i+1))
      = (∑ i ∈ Finset.range 458, stT186 (i+1)) + stT186 459 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 458
    simpa using h
  have hprev := st186_p458
  have hstep := st186_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p460 : ((4677313429781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT186 (i+1))
      = (∑ i ∈ Finset.range 459, stT186 (i+1)) + stT186 460 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 459
    simpa using h
  have hprev := st186_p459
  have hstep := st186_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p461 : ((4771536640057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT186 (i+1))
      = (∑ i ∈ Finset.range 460, stT186 (i+1)) + stT186 461 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 460
    simpa using h
  have hprev := st186_p460
  have hstep := st186_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p462 : ((5036808788859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT186 (i+1))
      = (∑ i ∈ Finset.range 461, stT186 (i+1)) + stT186 462 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 461
    simpa using h
  have hprev := st186_p461
  have hstep := st186_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p463 : ((1357520869653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT186 (i+1))
      = (∑ i ∈ Finset.range 462, stT186 (i+1)) + stT186 463 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 462
    simpa using h
  have hprev := st186_p462
  have hstep := st186_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p464 : ((368020510377/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT186 (i+1))
      = (∑ i ∈ Finset.range 463, stT186 (i+1)) + stT186 464 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 463
    simpa using h
  have hprev := st186_p463
  have hstep := st186_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p465 : ((3169381457013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT186 (i+1))
      = (∑ i ∈ Finset.range 464, stT186 (i+1)) + stT186 465 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 464
    simpa using h
  have hprev := st186_p464
  have hstep := st186_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p466 : ((3355226334357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT186 (i+1))
      = (∑ i ∈ Finset.range 465, stT186 (i+1)) + stT186 466 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 465
    simpa using h
  have hprev := st186_p465
  have hstep := st186_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p467 : ((3472705004613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT186 (i+1))
      = (∑ i ∈ Finset.range 466, stT186 (i+1)) + stT186 467 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 466
    simpa using h
  have hprev := st186_p466
  have hstep := st186_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p468 : ((875937139747/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT186 (i+1))
      = (∑ i ∈ Finset.range 467, stT186 (i+1)) + stT186 468 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 467
    simpa using h
  have hprev := st186_p467
  have hstep := st186_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p469 : ((3443881865167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT186 (i+1))
      = (∑ i ∈ Finset.range 468, stT186 (i+1)) + stT186 469 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 468
    simpa using h
  have hprev := st186_p468
  have hstep := st186_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p470 : ((825688979509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT186 (i+1))
      = (∑ i ∈ Finset.range 469, stT186 (i+1)) + stT186 470 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 469
    simpa using h
  have hprev := st186_p469
  have hstep := st186_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p471 : ((387809291339/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT186 (i+1))
      = (∑ i ∈ Finset.range 470, stT186 (i+1)) + stT186 471 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 470
    simpa using h
  have hprev := st186_p470
  have hstep := st186_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p472 : ((359255699243/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT186 (i+1))
      = (∑ i ∈ Finset.range 471, stT186 (i+1)) + stT186 472 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 471
    simpa using h
  have hprev := st186_p471
  have hstep := st186_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p473 : ((5305056831353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT186 (i+1))
      = (∑ i ∈ Finset.range 472, stT186 (i+1)) + stT186 473 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 472
    simpa using h
  have hprev := st186_p472
  have hstep := st186_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p474 : ((988655959833/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT186 (i+1))
      = (∑ i ∈ Finset.range 473, stT186 (i+1)) + stT186 474 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 473
    simpa using h
  have hprev := st186_p473
  have hstep := st186_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p475 : ((4717306874493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT186 (i+1))
      = (∑ i ∈ Finset.range 474, stT186 (i+1)) + stT186 475 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 474
    simpa using h
  have hprev := st186_p474
  have hstep := st186_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p476 : ((4660712566593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT186 (i+1))
      = (∑ i ∈ Finset.range 475, stT186 (i+1)) + stT186 476 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 475
    simpa using h
  have hprev := st186_p475
  have hstep := st186_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p477 : ((4781316371397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT186 (i+1))
      = (∑ i ∈ Finset.range 476, stT186 (i+1)) + stT186 477 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 476
    simpa using h
  have hprev := st186_p476
  have hstep := st186_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p478 : ((2530164803727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT186 (i+1))
      = (∑ i ∈ Finset.range 477, stT186 (i+1)) + stT186 478 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 477
    simpa using h
  have hprev := st186_p477
  have hstep := st186_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p479 : ((5455463955699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT186 (i+1))
      = (∑ i ∈ Finset.range 478, stT186 (i+1)) + stT186 479 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 478
    simpa using h
  have hprev := st186_p478
  have hstep := st186_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p480 : ((738441872583/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT186 (i+1))
      = (∑ i ∈ Finset.range 479, stT186 (i+1)) + stT186 480 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 479
    simpa using h
  have hprev := st186_p479
  have hstep := st186_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p481 : ((793675499103/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT186 (i+1))
      = (∑ i ∈ Finset.range 480, stT186 (i+1)) + stT186 481 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 480
    simpa using h
  have hprev := st186_p480
  have hstep := st186_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p482 : ((6715984940781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT186 (i+1))
      = (∑ i ∈ Finset.range 481, stT186 (i+1)) + stT186 482 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 481
    simpa using h
  have hprev := st186_p481
  have hstep := st186_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p483 : ((3476887662383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT186 (i+1))
      = (∑ i ∈ Finset.range 482, stT186 (i+1)) + stT186 483 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 482
    simpa using h
  have hprev := st186_p482
  have hstep := st186_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p484 : ((7028525704561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT186 (i+1))
      = (∑ i ∈ Finset.range 483, stT186 (i+1)) + stT186 484 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 483
    simpa using h
  have hprev := st186_p483
  have hstep := st186_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p485 : ((6930015515719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT186 (i+1))
      = (∑ i ∈ Finset.range 484, stT186 (i+1)) + stT186 485 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 484
    simpa using h
  have hprev := st186_p484
  have hstep := st186_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p486 : ((6673208296709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT186 (i+1))
      = (∑ i ∈ Finset.range 485, stT186 (i+1)) + stT186 486 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 485
    simpa using h
  have hprev := st186_p485
  have hstep := st186_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p487 : ((6295824082637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT186 (i+1))
      = (∑ i ∈ Finset.range 486, stT186 (i+1)) + stT186 487 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 486
    simpa using h
  have hprev := st186_p486
  have hstep := st186_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p488 : ((731577173839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT186 (i+1))
      = (∑ i ∈ Finset.range 487, stT186 (i+1)) + stT186 488 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 487
    simpa using h
  have hprev := st186_p487
  have hstep := st186_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p489 : ((675916280533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT186 (i+1))
      = (∑ i ∈ Finset.range 488, stT186 (i+1)) + stT186 489 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 488
    simpa using h
  have hprev := st186_p488
  have hstep := st186_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p490 : ((1255873009279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT186 (i+1))
      = (∑ i ∈ Finset.range 489, stT186 (i+1)) + stT186 490 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 489
    simpa using h
  have hprev := st186_p489
  have hstep := st186_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p491 : ((475539677477/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT186 (i+1))
      = (∑ i ∈ Finset.range 490, stT186 (i+1)) + stT186 491 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 490
    simpa using h
  have hprev := st186_p490
  have hstep := st186_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p492 : ((464052041009/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT186 (i+1))
      = (∑ i ∈ Finset.range 491, stT186 (i+1)) + stT186 492 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 491
    simpa using h
  have hprev := st186_p491
  have hstep := st186_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p493 : ((4694439094153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT186 (i+1))
      = (∑ i ∈ Finset.range 492, stT186 (i+1)) + stT186 493 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 492
    simpa using h
  have hprev := st186_p492
  have hstep := st186_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p494 : ((981784366781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT186 (i+1))
      = (∑ i ∈ Finset.range 493, stT186 (i+1)) + stT186 494 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 493
    simpa using h
  have hprev := st186_p493
  have hstep := st186_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p495 : ((5253335044657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT186 (i+1))
      = (∑ i ∈ Finset.range 494, stT186 (i+1)) + stT186 495 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 494
    simpa using h
  have hprev := st186_p494
  have hstep := st186_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p496 : ((1419800917393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT186 (i+1))
      = (∑ i ∈ Finset.range 495, stT186 (i+1)) + stT186 496 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 495
    simpa using h
  have hprev := st186_p495
  have hstep := st186_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p497 : ((3063564305037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT186 (i+1))
      = (∑ i ∈ Finset.range 496, stT186 (i+1)) + stT186 497 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 496
    simpa using h
  have hprev := st186_p496
  have hstep := st186_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p498 : ((1633783975461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT186 (i+1))
      = (∑ i ∈ Finset.range 497, stT186 (i+1)) + stT186 498 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 497
    simpa using h
  have hprev := st186_p497
  have hstep := st186_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p499 : ((3423615860607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT186 (i+1))
      = (∑ i ∈ Finset.range 498, stT186 (i+1)) + stT186 499 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 498
    simpa using h
  have hprev := st186_p498
  have hstep := st186_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_p500 : ((1404201681423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT186 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT186 (i+1))
      = (∑ i ∈ Finset.range 499, stT186 (i+1)) + stT186 500 := by
    have h := Finset.sum_range_succ (fun i => stT186 (i+1)) 499
    simpa using h
  have hprev := st186_p499
  have hstep := st186_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st186_s500 :
    |Real.sin (((186 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))
      - ((184279/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 2929139/10000000) (δ := 237/25000000) (ψ := -272131/200000) 186 184
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 186`** (evaluated boundary). -/
theorem station_186_sign : hardyG ((((186:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 186 500 (by norm_num) (by norm_num)
    ((-272131/200000 : ℚ) : ℝ)
  have hchain := st186_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT186 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((186 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-272131/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st186_c500
  have hsinb := abs_le.mp st186_s500
  have hbdy_lo : ((-76734368284719/691925000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((186 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-272131/200000 : ℚ) : ℝ))) / 2
          - ((((186:ℕ)):ℝ))
            * Real.sin (((186 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-272131/200000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((186:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((186:ℝ) * Real.log (500:ℝ) - ((-272131/200000 : ℚ) : ℝ))) / 2
        - ((186:ℝ)) * Real.sin ((186:ℝ) * Real.log (500:ℝ) - ((-272131/200000 : ℚ) : ℝ))
        ≥ ((-343166217/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((186:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-343166217/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-343166217/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-343166217/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((186:ℕ)):ℝ))+1) * (((((186:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2138883018769/7500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1404201681423/2000000000000 : ℚ) : ℝ) + ((-76734368284719/691925000000000 : ℚ) : ℝ)
      - ((2138883018769/7500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-272131/200000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((186:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-272131/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((186:ℕ)):ℝ)))).re
      - Real.sin ((-272131/200000 : ℚ) : ℝ)
        * (riemannZeta (line ((((186:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((186:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((186:ℕ)):ℝ))
      = (((((186:ℕ)):ℝ)) * (Real.log ((((186:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((186:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_186
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
  have hθwin : |(((-272131/200000 : ℚ) : ℝ) + ((36:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((186:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((186:ℕ)):ℝ)))
    (φ := ((-272131/200000 : ℚ) : ℝ) + ((36:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-272131/200000 : ℚ) : ℝ) + ((36:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-272131/200000 : ℚ)) : ℝ) - Real.pi) + ((36:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-272131/200000 : ℚ)) : ℝ) - Real.pi) 36).1,
    (cos_sin_shift ((((-272131/200000 : ℚ)) : ℝ) - Real.pi) 36).2]
  exact cos_sin_flip ((-272131/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_186_sign
end AxiomAudit
