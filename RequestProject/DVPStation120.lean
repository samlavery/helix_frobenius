import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 120` of the extended Hardy ladder (rung-126)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT120 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((120 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((345427/1000000 : ℚ) : ℝ))

theorem st120_c1 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((940931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53973/625000) (δ := 21/100000000) (ψ := 345427/1000000) 120 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t1 : ((940881/1000000 : ℚ) : ℝ) ≤ stT120 1 := by
  have hc : ((940881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((940881/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((940881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c2 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((203867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359633/1250000) (δ := 961/100000000) (ψ := 345427/1000000) 120 13
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t2 : ((720690219707/2500000000000 : ℚ) : ℝ) ≤ stT120 2 := by
  have hc : ((101921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((720690219707/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((101921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c3 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((179313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114711/1000000) (δ := 1047/100000000) (ψ := 345427/1000000) 120 21
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t3 : ((517603114553/1000000000000 : ℚ) : ℝ) ≤ stT120 3 := by
  have hc : ((179303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517603114553/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((179303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c4 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-880199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1323539/2000000) (δ := 7/1000000) (ψ := 345427/1000000) 120 26
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t4 : ((-4401245880249/10000000000000 : ℚ) : ℝ) ≤ stT120 4 := by
  have hc : ((-880249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4401245880249/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-880249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c5 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-81703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311191/625000) (δ := 1089/100000000) (ψ := 345427/1000000) 120 31
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t5 : ((-45678956121/250000000000 : ℚ) : ℝ) ≤ stT120 5 := by
  have hc : ((-81713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45678956121/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-81713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c6 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((508453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296761/5000000) (δ := 413/50000000) (ψ := 345427/1000000) 120 34
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t6 : ((1037773048123/5000000000000 : ℚ) : ℝ) ≤ stT120 6 := by
  have hc : ((508403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1037773048123/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((508403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c7 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((193457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428709/2500000) (δ := 1/160000) (ψ := 345427/1000000) 120 37
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t7 : ((365575671879/1250000000000 : ℚ) : ℝ) ≤ stT120 7 := by
  have hc : ((386889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365575671879/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((386889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c8 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-538839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1337409/2500000) (δ := 713/100000000) (ψ := 345427/1000000) 120 40
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t8 : ((-952630190863/5000000000000 : ℚ) : ℝ) ≤ stT120 8 := by
  have hc : ((-538889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-952630190863/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-538889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c9 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((840679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -357663/2500000) (δ := 57/6250000) (ψ := 345427/1000000) 120 42
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t9 : ((2802096386457/10000000000000 : ℚ) : ℝ) ≤ stT120 9 := by
  have hc : ((840629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2802096386457/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((840629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c10 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((879793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154803/1250000) (δ := 1093/100000000) (ψ := 345427/1000000) 120 44
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t10 : ((2781991054811/10000000000000 : ℚ) : ℝ) ≤ stT120 10 := by
  have hc : ((879743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2781991054811/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((879743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c11 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-839/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253831/625000) (δ := 7/800000) (ψ := 345427/1000000) 120 46
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t11 : ((-40512579261/2500000000000 : ℚ) : ℝ) ≤ stT120 11 := by
  have hc : ((-26873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40512579261/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-26873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c12 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-820831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6334153/10000000) (δ := 319/50000000) (ψ := 345427/1000000) 120 47
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t12 : ((-74052495891/312500000000 : ℚ) : ℝ) ≤ stT120 12 := by
  have hc : ((-820881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74052495891/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-820881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c13 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((90997/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1068961/10000000) (δ := 667/100000000) (ψ := 345427/1000000) 120 49
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t13 : ((31545789/125000000 : ℚ) : ℝ) ≤ stT120 13 := by
  have hc : ((5687/6250 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31545789/125000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((5687/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c14 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-574007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5455467/10000000) (δ := 443/50000000) (ψ := 345427/1000000) 120 50
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t14 : ((-1534232200941/10000000000000 : ℚ) : ℝ) ≤ stT120 14 := by
  have hc : ((-574057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1534232200941/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-574057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c15 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-50919/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2631299/5000000) (δ := 153/12500000) (ψ := 345427/1000000) 120 52
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t15 : ((-32871301959/250000000000 : ℚ) : ℝ) ≤ stT120 15 := by
  have hc : ((-12731/25000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32871301959/250000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-12731/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c16 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((799939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321801/2000000) (δ := 973/100000000) (ψ := 345427/1000000) 120 53
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t16 : ((799889/4000000 : ℚ) : ℝ) ≤ stT120 16 := by
  have hc : ((799889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799889/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((799889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c17 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((939999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 870419/10000000) (δ := 683/100000000) (ψ := 345427/1000000) 120 54
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t17 : ((569927736711/2500000000000 : ℚ) : ℝ) ≤ stT120 17 := by
  have hc : ((939949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569927736711/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((939949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c18 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((602639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115499/500000) (δ := 691/100000000) (ψ := 345427/1000000) 120 55
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t18 : ((710157764979/5000000000000 : ℚ) : ℝ) ≤ stT120 18 := by
  have hc : ((602589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((710157764979/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((602589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c19 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((427679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2822183/10000000) (δ := 471/50000000) (ψ := 345427/1000000) 120 56
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t19 : ((981048063753/10000000000000 : ℚ) : ℝ) ≤ stT120 19 := by
  have hc : ((427629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((981048063753/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((427629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c20 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((539559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39097/156250) (δ := 109/12500000) (ψ := 345427/1000000) 120 57
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t20 : ((1206378271103/10000000000000 : ℚ) : ℝ) ≤ stT120 20 := by
  have hc : ((539509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1206378271103/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((539509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c21 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((42027/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715647/5000000) (δ := 19/2500000) (ψ := 345427/1000000) 120 58
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t21 : ((91704939361/500000000000 : ℚ) : ℝ) ≤ stT120 21 := by
  have hc : ((84049/100000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91704939361/500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((84049/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c22 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((198357/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64133/2000000) (δ := 307/50000000) (ψ := 345427/1000000) 120 59
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t22 : ((422877192429/2000000000000 : ℚ) : ℝ) ≤ stT120 22 := by
  have hc : ((198347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422877192429/2000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((198347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c23 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((473761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2693099/10000000) (δ := 509/50000000) (ψ := 345427/1000000) 120 60
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t23 : ((123469456173/1250000000000 : ℚ) : ℝ) ≤ stT120 23 := by
  have hc : ((473711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123469456173/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((473711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c24 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-126143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2816589/5000000) (δ := 53/6250000) (ψ := 345427/1000000) 120 61
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t24 : ((-128754401013/1000000000000 : ℚ) : ℝ) ≤ stT120 24 := by
  have hc : ((-126153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128754401013/1000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-126153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c25 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-439693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330671/500000) (δ := 29/3125000) (ψ := 345427/1000000) 120 61
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t25 : ((-439718219859/2500000000000 : ℚ) : ℝ) ≤ stT120 25 := by
  have hc : ((-219859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439718219859/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-219859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c26 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((120323/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2671671/10000000) (δ := 757/100000000) (ψ := 345427/1000000) 120 62
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t26 : ((471896520981/5000000000000 : ℚ) : ℝ) ≤ stT120 26 := by
  have hc : ((240621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471896520981/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((240621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c27 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((77399/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857097/5000000) (δ := 777/100000000) (ψ := 345427/1000000) 120 63
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t27 : ((148944753/1000000000 : ℚ) : ℝ) ≤ stT120 27 := by
  have hc : ((38697/50000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148944753/1000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((38697/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c28 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-34373/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -813983/1250000) (δ := 137/12500000) (ψ := 345427/1000000) 120 64
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t28 : ((-20788053/128000000 : ℚ) : ℝ) ≤ stT120 28 := by
  have hc : ((-55/64 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20788053/128000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-55/64 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c29 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-35409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1003883/2500000) (δ := 107/12500000) (ψ := 345427/1000000) 120 64
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t29 : ((-32922865943/5000000000000 : ℚ) : ℝ) ≤ stT120 29 := by
  have hc : ((-35459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32922865943/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-35459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c30 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((820343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760983/5000000) (δ := 479/50000000) (ψ := 345427/1000000) 120 65
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t30 : ((1497642562113/10000000000000 : ℚ) : ℝ) ≤ stT120 30 := by
  have hc : ((820293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1497642562113/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((820293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c31 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-491523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3696491/5000000) (δ := 577/50000000) (ψ := 345427/1000000) 120 66
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t31 : ((-110355843949/625000000000 : ℚ) : ℝ) ≤ stT120 31 := by
  have hc : ((-122887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110355843949/625000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-122887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c32 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((657989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2131627/10000000) (δ := 597/50000000) (ψ := 345427/1000000) 120 66
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t32 : ((581541097137/5000000000000 : ℚ) : ℝ) ≤ stT120 32 := by
  have hc : ((657939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581541097137/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((657939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c33 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-83181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4344839/10000000) (δ := 7/1000000) (ψ := 345427/1000000) 120 67
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t33 : ((-72421545531/2500000000000 : ℚ) : ℝ) ≤ stT120 33 := by
  have hc : ((-41603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72421545531/2500000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-41603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c34 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-135111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92221/200000) (δ := 943/100000000) (ψ := 345427/1000000) 120 67
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t34 : ((-3621192939/78125000000 : ℚ) : ℝ) ≤ stT120 34 := by
  have hc : ((-4223/15625 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3621192939/78125000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-4223/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c35 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((286653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -600163/2500000) (δ := 71/10000000) (ψ := 345427/1000000) 120 68
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t35 : ((30280600089/312500000000 : ℚ) : ℝ) ≤ stT120 35 := by
  have hc : ((71657/125000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30280600089/312500000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((71657/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c36 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-187729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6050611/10000000) (δ := 773/100000000) (ψ := 345427/1000000) 120 68
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t36 : ((-625805125161/5000000000000 : ℚ) : ℝ) ≤ stT120 36 := by
  have hc : ((-375483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625805125161/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-375483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c37 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((839157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71883/500000) (δ := 541/50000000) (ψ := 345427/1000000) 120 69
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t37 : ((1379482677823/10000000000000 : ℚ) : ℝ) ≤ stT120 37 := by
  have hc : ((839107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1379482677823/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((839107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c38 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-869569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3281407/5000000) (δ := 681/100000000) (ψ := 345427/1000000) 120 69
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t38 : ((-282141797217/2000000000000 : ℚ) : ℝ) ≤ stT120 38 := by
  have hc : ((-869619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282141797217/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-869619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c39 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((857193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1352503/10000000) (δ := 671/100000000) (ψ := 345427/1000000) 120 70
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t39 : ((1372526800183/10000000000000 : ℚ) : ℝ) ≤ stT120 39 := by
  have hc : ((857143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1372526800183/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((857143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c40 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-399713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6242839/10000000) (δ := 153/25000000) (ψ := 345427/1000000) 120 70
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t40 : ((-316020670791/2500000000000 : ℚ) : ℝ) ≤ stT120 40 := by
  have hc : ((-199869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316020670791/2500000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-199869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c41 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((85009/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102867/500000) (δ := 391/50000000) (ψ := 345427/1000000) 120 71
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t41 : ((531007759107/5000000000000 : ℚ) : ℝ) ≤ stT120 41 := by
  have hc : ((340011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531007759107/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((340011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c42 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-238823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 206877/400000) (δ := 1021/100000000) (ψ := 345427/1000000) 120 71
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t42 : ((-719825361/9765625000 : ℚ) : ℝ) ≤ stT120 42 := by
  have hc : ((-7464/15625 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-719825361/9765625000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-7464/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c43 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((17907/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3476889/10000000) (δ := 21/2000000) (ψ := 345427/1000000) 120 72
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t43 : ((2730028147/100000000000 : ℚ) : ℝ) ≤ stT120 43 := by
  have hc : ((8951/50000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2730028147/100000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((8951/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c44 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((100711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3419967/10000000) (δ := 81/10000000) (ψ := 345427/1000000) 120 72
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t44 : ((18973722927/625000000000 : ℚ) : ℝ) ≤ stT120 44 := by
  have hc : ((50343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18973722927/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((50343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c45 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-301661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277307/500000) (δ := 261/25000000) (ψ := 345427/1000000) 120 73
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t45 : ((-28107933777/312500000000 : ℚ) : ℝ) ≤ stT120 45 := by
  have hc : ((-150843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28107933777/312500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-150843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c46 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((913491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 261883/2500000) (δ := 281/25000000) (ψ := 345427/1000000) 120 73
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t46 : ((1346794765779/10000000000000 : ℚ) : ℝ) ≤ stT120 46 := by
  have hc : ((913441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1346794765779/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((913441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c47 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-494979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3749697/5000000) (δ := 1199/100000000) (ψ := 345427/1000000) 120 73
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t47 : ((-3610187923/25000000000 : ℚ) : ℝ) ≤ stT120 47 := by
  have hc : ((-123751/125000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3610187923/25000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-123751/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c48 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((726887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1892547/10000000) (δ := 277/25000000) (ψ := 345427/1000000) 120 74
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t48 : ((8392786839/80000000000 : ℚ) : ℝ) ≤ stT120 48 := by
  have hc : ((726837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8392786839/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((726837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c49 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-18247/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107331/250000) (δ := 47/4000000) (ψ := 345427/1000000) 120 74
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t49 : ((-26076081859/1250000000000 : ℚ) : ℝ) ≤ stT120 49 := by
  have hc : ((-73013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26076081859/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-73013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c50 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-540279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5353911/10000000) (δ := 569/50000000) (ψ := 345427/1000000) 120 75
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t50 : ((-382070418203/5000000000000 : ℚ) : ℝ) ≤ stT120 50 := by
  have hc : ((-540329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382070418203/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-540329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c51 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((243143/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 586877/10000000) (δ := 409/50000000) (ψ := 345427/1000000) 120 75
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t51 : ((17022538827/125000000000 : ℚ) : ℝ) ≤ stT120 51 := by
  have hc : ((486261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17022538827/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((486261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c52 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-419141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3206151/5000000) (δ := 509/50000000) (ψ := 345427/1000000) 120 75
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t52 : ((-290639434833/2500000000000 : ℚ) : ℝ) ≤ stT120 52 := by
  have hc : ((-209583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290639434833/2500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-209583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c53 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((1103/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1790601/5000000) (δ := 1047/100000000) (ψ := 345427/1000000) 120 76
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t53 : ((1514536873/80000000000 : ℚ) : ℝ) ≤ stT120 53 := by
  have hc : ((5513/40000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1514536873/80000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((5513/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c54 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((344541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1013219/5000000) (δ := 647/100000000) (ψ := 345427/1000000) 120 76
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t54 : ((117206668683/1250000000000 : ℚ) : ℝ) ≤ stT120 54 := by
  have hc : ((86129/125000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117206668683/1250000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((86129/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c55 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-39667/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7531179/10000000) (δ := 249/25000000) (ψ := 345427/1000000) 120 76
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t55 : ((-133724199/1000000000 : ℚ) : ℝ) ≤ stT120 55 := by
  have hc : ((-39669/40000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133724199/1000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-39669/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c56 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((446011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86601/312500) (δ := 1087/100000000) (ψ := 345427/1000000) 120 77
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t56 : ((297970180033/5000000000000 : ℚ) : ℝ) ≤ stT120 56 := by
  have hc : ((445961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297970180033/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((445961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c57 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((8238/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2538641/10000000) (δ := 807/100000000) (ψ := 345427/1000000) 120 77
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t57 : ((87283678603/1250000000000 : ℚ) : ℝ) ≤ stT120 57 := by
  have hc : ((263591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87283678603/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((263591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c58 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-199847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1939041/2500000) (δ := 269/25000000) (ψ := 345427/1000000) 120 77
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t58 : ((-52485046341/400000000000 : ℚ) : ℝ) ≤ stT120 58 := by
  have hc : ((-199857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52485046341/400000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-199857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c59 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((427213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -282347/1000000) (δ := 141/20000000) (ψ := 345427/1000000) 120 78
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t59 : ((556118810907/10000000000000 : ℚ) : ℝ) ≤ stT120 59 := by
  have hc : ((427163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((556118810907/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((427163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c60 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((631379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1109333/5000000) (δ := 369/50000000) (ψ := 345427/1000000) 120 78
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t60 : ((407520975513/5000000000000 : ℚ) : ℝ) ≤ stT120 60 := by
  have hc : ((631329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407520975513/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((631329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c61 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-120451/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448591/625000) (δ := 369/50000000) (ψ := 345427/1000000) 120 78
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t61 : ((-616918914901/5000000000000 : ℚ) : ℝ) ≤ stT120 61 := by
  have hc : ((-481829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-616918914901/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-481829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c62 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((21927/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3652351/10000000) (δ := 247/25000000) (ψ := 345427/1000000) 120 79
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t62 : ((27834611917/2000000000000 : ℚ) : ℝ) ≤ stT120 62 := by
  have hc : ((21917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27834611917/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((21917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c63 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((896451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143469/1250000) (δ := 179/20000000) (ψ := 345427/1000000) 120 79
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t63 : ((1129358588281/10000000000000 : ℚ) : ℝ) ≤ stT120 63 := by
  have hc : ((896401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1129358588281/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((896401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c64 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-701933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5872259/10000000) (δ := 247/25000000) (ψ := 345427/1000000) 120 79
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t64 : ((-877479451983/10000000000000 : ℚ) : ℝ) ≤ stT120 64 := by
  have hc : ((-701983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-877479451983/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-701983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c65 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-482041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81007/156250) (δ := 839/100000000) (ψ := 345427/1000000) 120 80
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t65 : ((-149490151917/2500000000000 : ℚ) : ℝ) ≤ stT120 65 := by
  have hc : ((-482091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149490151917/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-482091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c66 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((970937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604207/10000000) (δ := 181/25000000) (ψ := 345427/1000000) 120 80
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t66 : ((597539200359/5000000000000 : ℚ) : ℝ) ≤ stT120 66 := by
  have hc : ((970887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((597539200359/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((970887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c67 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((3967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976789/2500000) (δ := 251/25000000) (ψ := 345427/1000000) 120 80
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t67 : ((1203979437/1250000000000 : ℚ) : ℝ) ≤ stT120 67 := by
  have hc : ((1971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1203979437/1250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((1971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c68 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-980249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7356281/10000000) (δ := 1153/100000000) (ψ := 345427/1000000) 120 81
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t68 : ((-1188788011021/10000000000000 : ℚ) : ℝ) ≤ stT120 68 := by
  have hc : ((-980299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1188788011021/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-980299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c69 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((7421/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2976641/10000000) (δ := 1153/100000000) (ψ := 345427/1000000) 120 81
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t69 : ((223315659/5000000000 : ℚ) : ℝ) ≤ stT120 69 := by
  have hc : ((371/1000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223315659/5000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((371/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c70 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((429881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66999/500000) (δ := 713/100000000) (ψ := 345427/1000000) 120 81
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t70 : ((4013874431/39062500000 : ℚ) : ℝ) ≤ stT120 70 := by
  have hc : ((13433/15625 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4013874431/39062500000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((13433/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c71 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-154727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559537/1000000) (δ := 89/10000000) (ψ := 345427/1000000) 120 81
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t71 : ((-183642053289/2500000000000 : ℚ) : ℝ) ≤ stT120 71 := by
  have hc : ((-309479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183642053289/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-309479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c72 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-89311/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73959/125000) (δ := 983/100000000) (ψ := 345427/1000000) 120 82
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t72 : ((-26315362733/312500000000 : ℚ) : ℝ) ≤ stT120 72 := by
  have hc : ((-357269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26315362733/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-357269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c73 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((75739/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -444681/2500000) (δ := 743/100000000) (ψ := 345427/1000000) 120 82
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t73 : ((44319953337/500000000000 : ℚ) : ℝ) ≤ stT120 73 := by
  have hc : ((37867/50000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44319953337/500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((37867/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c74 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((302437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 575743/2500000) (δ := 11/1000000) (ψ := 345427/1000000) 120 82
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t74 : ((21971668257/312500000000 : ℚ) : ℝ) ≤ stT120 74 := by
  have hc : ((75603/125000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21971668257/312500000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((75603/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c75 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-819853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3164939/5000000) (δ := 1063/100000000) (ψ := 345427/1000000) 120 82
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t75 : ((-946742814003/10000000000000 : ℚ) : ℝ) ≤ stT120 75 := by
  have hc : ((-819903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-946742814003/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-819903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c76 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-1393/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5404517/10000000) (δ := 183/25000000) (ψ := 345427/1000000) 120 83
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t76 : ((-2556839091/40000000000 : ℚ) : ℝ) ≤ stT120 76 := by
  have hc : ((-2229/4000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2556839091/40000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-2229/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c77 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((41459/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1482893/10000000) (δ := 243/25000000) (ψ := 345427/1000000) 120 83
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t77 : ((18897613873/200000000000 : ℚ) : ℝ) ≤ stT120 77 := by
  have hc : ((82913/100000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18897613873/200000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((82913/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c78 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((577403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2388129/10000000) (δ := 223/25000000) (ψ := 345427/1000000) 120 83
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t78 : ((653723522781/10000000000000 : ℚ) : ℝ) ≤ stT120 78 := by
  have hc : ((577353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((653723522781/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((577353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c79 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-395713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6209837/10000000) (δ := 631/100000000) (ψ := 345427/1000000) 120 83
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t79 : ((-6956876171/78125000000 : ℚ) : ℝ) ≤ stT120 79 := by
  have hc : ((-197869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6956876171/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-197869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c80 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-658633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1431123/2500000) (δ := 801/100000000) (ψ := 345427/1000000) 120 84
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t80 : ((-368214994611/5000000000000 : ℚ) : ℝ) ≤ stT120 80 := by
  have hc : ((-658683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368214994611/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-658683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c81 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((174339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249717/1250000) (δ := 321/50000000) (ψ := 345427/1000000) 120 84
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t81 : ((387392183483/5000000000000 : ℚ) : ℝ) ≤ stT120 81 := by
  have hc : ((348653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387392183483/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((348653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c82 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((390879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420823/2500000) (δ := 641/100000000) (ψ := 345427/1000000) 120 84
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t82 : ((43162593501/500000000000 : ℚ) : ℝ) ≤ stT120 82 := by
  have hc : ((195427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43162593501/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((195427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c83 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-528713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53197/100000) (δ := 1121/100000000) (ψ := 345427/1000000) 120 84
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t83 : ((-580393005609/10000000000000 : ℚ) : ℝ) ≤ stT120 83 := by
  have hc : ((-528763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-580393005609/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-528763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c84 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-182337/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3397703/5000000) (δ := 123/10000000) (ψ := 345427/1000000) 120 85
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t84 : ((-19895698823/200000000000 : ℚ) : ℝ) ≤ stT120 84 := by
  have hc : ((-182347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19895698823/200000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-182347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c85 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((269399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3245069/10000000) (δ := 653/100000000) (ψ := 345427/1000000) 120 85
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t85 : ((73037482887/2500000000000 : ℚ) : ℝ) ≤ stT120 85 := by
  have hc : ((269349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73037482887/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((269349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c86 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((24861/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 263743/10000000) (δ := 1133/100000000) (ψ := 345427/1000000) 120 85
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t86 : ((107227758553/1000000000000 : ℚ) : ℝ) ≤ stT120 86 := by
  have hc : ((99439/100000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107227758553/1000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((99439/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c87 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((77921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373199/1000000) (δ := 99/10000000) (ψ := 345427/1000000) 120 85
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t87 : ((5217902097/625000000000 : ℚ) : ℝ) ≤ stT120 87 := by
  have hc : ((77871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5217902097/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((77871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c88 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-120223/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7160599/10000000) (δ := 103/10000000) (ψ := 345427/1000000) 120 85
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t88 : ((-128164861417/1250000000000 : ℚ) : ℝ) ≤ stT120 88 := by
  have hc : ((-480917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128164861417/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-480917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c89 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-59071/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2578749/5000000) (δ := 823/100000000) (ψ := 345427/1000000) 120 86
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t89 : ((-125243533691/2500000000000 : ℚ) : ℝ) ≤ stT120 89 := by
  have hc : ((-236309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125243533691/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-236309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c90 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((750351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451377/2500000) (δ := 823/100000000) (ψ := 345427/1000000) 120 86
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t90 : ((197721570423/2500000000000 : ℚ) : ℝ) ≤ stT120 90 := by
  have hc : ((750301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197721570423/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((750301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c91 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((823197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1509443/10000000) (δ := 1263/100000000) (ψ := 345427/1000000) 120 86
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t91 : ((215722957437/2500000000000 : ℚ) : ℝ) ≤ stT120 91 := by
  have hc : ((823147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215722957437/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((823147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c92 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-337697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1197041/2500000) (δ := 903/100000000) (ψ := 345427/1000000) 120 86
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t92 : ((-352125903031/10000000000000 : ℚ) : ℝ) ≤ stT120 92 := by
  have hc : ((-337747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352125903031/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-337747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c93 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-498741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1919131/2500000) (δ := 557/50000000) (ψ := 345427/1000000) 120 87
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t93 : ((-32324775077/312500000000 : ℚ) : ℝ) ≤ stT120 93 := by
  have hc : ((-249383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32324775077/312500000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-249383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c94 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-107347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2233969/5000000) (δ := 477/50000000) (ψ := 345427/1000000) 120 87
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t94 : ((-13843230373/625000000000 : ℚ) : ℝ) ≤ stT120 94 := by
  have hc : ((-26843/125000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13843230373/625000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-26843/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c95 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((869147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258661/2000000) (δ := 537/50000000) (ψ := 345427/1000000) 120 87
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t95 : ((445837200933/5000000000000 : ℚ) : ℝ) ≤ stT120 95 := by
  have hc : ((869097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445837200933/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((869097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c96 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((147797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 369617/2000000) (δ := 537/50000000) (ψ := 345427/1000000) 120 87
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t96 : ((7541718397/100000000000 : ℚ) : ℝ) ≤ stT120 96 := by
  have hc : ((147787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7541718397/100000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((147787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c97 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-400417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4956921/10000000) (δ := 457/50000000) (ψ := 345427/1000000) 120 87
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t97 : ((-406612967049/10000000000000 : ℚ) : ℝ) ≤ stT120 97 := by
  have hc : ((-400467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406612967049/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-400467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c98 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-249353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1918523/2500000) (δ := 37/4000000) (ψ := 345427/1000000) 120 88
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t98 : ((-503794615843/5000000000000 : ℚ) : ℝ) ≤ stT120 98 := by
  have hc : ((-498731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503794615843/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-498731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c99 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((-27689/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4628381/10000000) (δ := 319/50000000) (ψ := 345427/1000000) 120 88
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t99 : ((-6958380593/250000000000 : ℚ) : ℝ) ≤ stT120 99 := by
  have hc : ((-13847/50000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6958380593/250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-13847/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_c100 :
    |Real.cos (((120 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((345427/1000000 : ℚ) : ℝ))
      - ((12483/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10083/62500) (δ := 201/20000000) (ψ := 345427/1000000) 120 88
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st120_t100 : ((399430600569/5000000000000 : ℚ) : ℝ) ≤ stT120 100 := by
  have hc : ((399431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((120 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((345427/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st120_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399430600569/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((399431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st120_p1 : ((940881/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT120 (i+1) := by
  rw [Finset.sum_range_one]
  exact st120_t1

theorem st120_p2 : ((3072892719707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT120 (i+1))
      = (∑ i ∈ Finset.range 1, stT120 (i+1)) + stT120 2 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 1
    simpa using h
  have hprev := st120_p1
  have hstep := st120_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p3 : ((8733801012179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT120 (i+1))
      = (∑ i ∈ Finset.range 2, stT120 (i+1)) + stT120 3 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 2
    simpa using h
  have hprev := st120_p2
  have hstep := st120_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p4 : ((13066356144109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT120 (i+1))
      = (∑ i ∈ Finset.range 3, stT120 (i+1)) + stT120 4 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 3
    simpa using h
  have hprev := st120_p3
  have hstep := st120_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p5 : ((11239197899269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT120 (i+1))
      = (∑ i ∈ Finset.range 4, stT120 (i+1)) + stT120 5 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 4
    simpa using h
  have hprev := st120_p4
  have hstep := st120_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p6 : ((2662948799103/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT120 (i+1))
      = (∑ i ∈ Finset.range 5, stT120 (i+1)) + stT120 6 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 5
    simpa using h
  have hprev := st120_p5
  have hstep := st120_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p7 : ((16239349370547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT120 (i+1))
      = (∑ i ∈ Finset.range 6, stT120 (i+1)) + stT120 7 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 6
    simpa using h
  have hprev := st120_p6
  have hstep := st120_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p8 : ((14334088988821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT120 (i+1))
      = (∑ i ∈ Finset.range 7, stT120 (i+1)) + stT120 8 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 7
    simpa using h
  have hprev := st120_p7
  have hstep := st120_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p9 : ((8568092687639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT120 (i+1))
      = (∑ i ∈ Finset.range 8, stT120 (i+1)) + stT120 9 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 8
    simpa using h
  have hprev := st120_p8
  have hstep := st120_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p10 : ((19918176430089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT120 (i+1))
      = (∑ i ∈ Finset.range 9, stT120 (i+1)) + stT120 10 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 9
    simpa using h
  have hprev := st120_p9
  have hstep := st120_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p11 : ((3951225222609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT120 (i+1))
      = (∑ i ∈ Finset.range 10, stT120 (i+1)) + stT120 11 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 10
    simpa using h
  have hprev := st120_p10
  have hstep := st120_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p12 : ((17386446244533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT120 (i+1))
      = (∑ i ∈ Finset.range 11, stT120 (i+1)) + stT120 12 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 11
    simpa using h
  have hprev := st120_p11
  have hstep := st120_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p13 : ((19910109364533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT120 (i+1))
      = (∑ i ∈ Finset.range 12, stT120 (i+1)) + stT120 13 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 12
    simpa using h
  have hprev := st120_p12
  have hstep := st120_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p14 : ((2296984645449/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT120 (i+1))
      = (∑ i ∈ Finset.range 13, stT120 (i+1)) + stT120 14 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 13
    simpa using h
  have hprev := st120_p13
  have hstep := st120_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p15 : ((1066314067827/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT120 (i+1))
      = (∑ i ∈ Finset.range 14, stT120 (i+1)) + stT120 15 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 14
    simpa using h
  have hprev := st120_p14
  have hstep := st120_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p16 : ((1191296724077/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT120 (i+1))
      = (∑ i ∈ Finset.range 15, stT120 (i+1)) + stT120 16 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 15
    simpa using h
  have hprev := st120_p15
  have hstep := st120_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p17 : ((5335114633019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT120 (i+1))
      = (∑ i ∈ Finset.range 16, stT120 (i+1)) + stT120 17 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 16
    simpa using h
  have hprev := st120_p16
  have hstep := st120_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p18 : ((11380387031017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT120 (i+1))
      = (∑ i ∈ Finset.range 17, stT120 (i+1)) + stT120 18 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 17
    simpa using h
  have hprev := st120_p17
  have hstep := st120_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p19 : ((23741822125787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT120 (i+1))
      = (∑ i ∈ Finset.range 18, stT120 (i+1)) + stT120 19 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 18
    simpa using h
  have hprev := st120_p18
  have hstep := st120_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p20 : ((2494820039689/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT120 (i+1))
      = (∑ i ∈ Finset.range 19, stT120 (i+1)) + stT120 20 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 19
    simpa using h
  have hprev := st120_p19
  have hstep := st120_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p21 : ((2678229918411/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT120 (i+1))
      = (∑ i ∈ Finset.range 20, stT120 (i+1)) + stT120 21 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 20
    simpa using h
  have hprev := st120_p20
  have hstep := st120_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p22 : ((5779337029251/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT120 (i+1))
      = (∑ i ∈ Finset.range 21, stT120 (i+1)) + stT120 22 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 21
    simpa using h
  have hprev := st120_p21
  have hstep := st120_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p23 : ((29884440795639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT120 (i+1))
      = (∑ i ∈ Finset.range 22, stT120 (i+1)) + stT120 23 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 22
    simpa using h
  have hprev := st120_p22
  have hstep := st120_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p24 : ((28596896785509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT120 (i+1))
      = (∑ i ∈ Finset.range 23, stT120 (i+1)) + stT120 24 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 23
    simpa using h
  have hprev := st120_p23
  have hstep := st120_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p25 : ((26838023906073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT120 (i+1))
      = (∑ i ∈ Finset.range 24, stT120 (i+1)) + stT120 25 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 24
    simpa using h
  have hprev := st120_p24
  have hstep := st120_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p26 : ((5556363389607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT120 (i+1))
      = (∑ i ∈ Finset.range 25, stT120 (i+1)) + stT120 26 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 25
    simpa using h
  have hprev := st120_p25
  have hstep := st120_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p27 : ((5854252895607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT120 (i+1))
      = (∑ i ∈ Finset.range 26, stT120 (i+1)) + stT120 27 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 26
    simpa using h
  have hprev := st120_p26
  have hstep := st120_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p28 : ((2764719783741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT120 (i+1))
      = (∑ i ∈ Finset.range 27, stT120 (i+1)) + stT120 28 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 27
    simpa using h
  have hprev := st120_p27
  have hstep := st120_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p29 : ((6895338026381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT120 (i+1))
      = (∑ i ∈ Finset.range 28, stT120 (i+1)) + stT120 29 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 28
    simpa using h
  have hprev := st120_p28
  have hstep := st120_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p30 : ((29078994667637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT120 (i+1))
      = (∑ i ∈ Finset.range 29, stT120 (i+1)) + stT120 30 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 29
    simpa using h
  have hprev := st120_p29
  have hstep := st120_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p31 : ((27313301164453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT120 (i+1))
      = (∑ i ∈ Finset.range 30, stT120 (i+1)) + stT120 31 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 30
    simpa using h
  have hprev := st120_p30
  have hstep := st120_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p32 : ((28476383358727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT120 (i+1))
      = (∑ i ∈ Finset.range 31, stT120 (i+1)) + stT120 32 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 31
    simpa using h
  have hprev := st120_p31
  have hstep := st120_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p33 : ((28186697176603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT120 (i+1))
      = (∑ i ∈ Finset.range 32, stT120 (i+1)) + stT120 33 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 32
    simpa using h
  have hprev := st120_p32
  have hstep := st120_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p34 : ((27723184480411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT120 (i+1))
      = (∑ i ∈ Finset.range 33, stT120 (i+1)) + stT120 34 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 33
    simpa using h
  have hprev := st120_p33
  have hstep := st120_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p35 : ((28692163683259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT120 (i+1))
      = (∑ i ∈ Finset.range 34, stT120 (i+1)) + stT120 35 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 34
    simpa using h
  have hprev := st120_p34
  have hstep := st120_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p36 : ((27440553432937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT120 (i+1))
      = (∑ i ∈ Finset.range 35, stT120 (i+1)) + stT120 36 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 35
    simpa using h
  have hprev := st120_p35
  have hstep := st120_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p37 : ((720500902769/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT120 (i+1))
      = (∑ i ∈ Finset.range 36, stT120 (i+1)) + stT120 37 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 36
    simpa using h
  have hprev := st120_p36
  have hstep := st120_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p38 : ((1096373084987/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT120 (i+1))
      = (∑ i ∈ Finset.range 37, stT120 (i+1)) + stT120 38 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 37
    simpa using h
  have hprev := st120_p37
  have hstep := st120_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p39 : ((14390926962429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT120 (i+1))
      = (∑ i ∈ Finset.range 38, stT120 (i+1)) + stT120 39 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 38
    simpa using h
  have hprev := st120_p38
  have hstep := st120_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p40 : ((13758885620847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT120 (i+1))
      = (∑ i ∈ Finset.range 39, stT120 (i+1)) + stT120 40 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 39
    simpa using h
  have hprev := st120_p39
  have hstep := st120_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p41 : ((7144946689977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT120 (i+1))
      = (∑ i ∈ Finset.range 40, stT120 (i+1)) + stT120 41 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 40
    simpa using h
  have hprev := st120_p40
  have hstep := st120_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p42 : ((6960671397561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT120 (i+1))
      = (∑ i ∈ Finset.range 41, stT120 (i+1)) + stT120 42 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 41
    simpa using h
  have hprev := st120_p41
  have hstep := st120_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p43 : ((1757230525309/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT120 (i+1))
      = (∑ i ∈ Finset.range 42, stT120 (i+1)) + stT120 43 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 42
    simpa using h
  have hprev := st120_p42
  have hstep := st120_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p44 : ((444051062059/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT120 (i+1))
      = (∑ i ∈ Finset.range 43, stT120 (i+1)) + stT120 44 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 43
    simpa using h
  have hprev := st120_p43
  have hstep := st120_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p45 : ((859994190341/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT120 (i+1))
      = (∑ i ∈ Finset.range 44, stT120 (i+1)) + stT120 45 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 44
    simpa using h
  have hprev := st120_p44
  have hstep := st120_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p46 : ((28866608856691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT120 (i+1))
      = (∑ i ∈ Finset.range 45, stT120 (i+1)) + stT120 46 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 45
    simpa using h
  have hprev := st120_p45
  have hstep := st120_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p47 : ((27422533687491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT120 (i+1))
      = (∑ i ∈ Finset.range 46, stT120 (i+1)) + stT120 47 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 46
    simpa using h
  have hprev := st120_p46
  have hstep := st120_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p48 : ((14235816021183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT120 (i+1))
      = (∑ i ∈ Finset.range 47, stT120 (i+1)) + stT120 48 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 47
    simpa using h
  have hprev := st120_p47
  have hstep := st120_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p49 : ((14131511693747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT120 (i+1))
      = (∑ i ∈ Finset.range 48, stT120 (i+1)) + stT120 49 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 48
    simpa using h
  have hprev := st120_p48
  have hstep := st120_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p50 : ((1718680159443/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT120 (i+1))
      = (∑ i ∈ Finset.range 49, stT120 (i+1)) + stT120 50 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 49
    simpa using h
  have hprev := st120_p49
  have hstep := st120_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p51 : ((901896426789/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT120 (i+1))
      = (∑ i ∈ Finset.range 50, stT120 (i+1)) + stT120 51 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 50
    simpa using h
  have hprev := st120_p50
  have hstep := st120_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p52 : ((6924531979479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT120 (i+1))
      = (∑ i ∈ Finset.range 51, stT120 (i+1)) + stT120 52 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 51
    simpa using h
  have hprev := st120_p51
  have hstep := st120_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p53 : ((27887445027041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT120 (i+1))
      = (∑ i ∈ Finset.range 52, stT120 (i+1)) + stT120 53 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 52
    simpa using h
  have hprev := st120_p52
  have hstep := st120_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p54 : ((5765019675301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT120 (i+1))
      = (∑ i ∈ Finset.range 53, stT120 (i+1)) + stT120 54 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 53
    simpa using h
  have hprev := st120_p53
  have hstep := st120_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p55 : ((5497571277301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT120 (i+1))
      = (∑ i ∈ Finset.range 54, stT120 (i+1)) + stT120 55 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 54
    simpa using h
  have hprev := st120_p54
  have hstep := st120_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p56 : ((28083796746571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT120 (i+1))
      = (∑ i ∈ Finset.range 55, stT120 (i+1)) + stT120 56 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 55
    simpa using h
  have hprev := st120_p55
  have hstep := st120_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p57 : ((5756413235079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT120 (i+1))
      = (∑ i ∈ Finset.range 56, stT120 (i+1)) + stT120 57 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 56
    simpa using h
  have hprev := st120_p56
  have hstep := st120_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p58 : ((2746994001687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT120 (i+1))
      = (∑ i ∈ Finset.range 57, stT120 (i+1)) + stT120 58 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 57
    simpa using h
  have hprev := st120_p57
  have hstep := st120_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p59 : ((28026058827777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT120 (i+1))
      = (∑ i ∈ Finset.range 58, stT120 (i+1)) + stT120 59 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 58
    simpa using h
  have hprev := st120_p58
  have hstep := st120_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p60 : ((28841100778803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT120 (i+1))
      = (∑ i ∈ Finset.range 59, stT120 (i+1)) + stT120 60 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 59
    simpa using h
  have hprev := st120_p59
  have hstep := st120_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p61 : ((27607262949001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT120 (i+1))
      = (∑ i ∈ Finset.range 60, stT120 (i+1)) + stT120 61 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 60
    simpa using h
  have hprev := st120_p60
  have hstep := st120_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p62 : ((13873218004293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT120 (i+1))
      = (∑ i ∈ Finset.range 61, stT120 (i+1)) + stT120 62 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 61
    simpa using h
  have hprev := st120_p61
  have hstep := st120_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p63 : ((28875794596867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT120 (i+1))
      = (∑ i ∈ Finset.range 62, stT120 (i+1)) + stT120 63 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 62
    simpa using h
  have hprev := st120_p62
  have hstep := st120_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p64 : ((6999578786221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT120 (i+1))
      = (∑ i ∈ Finset.range 63, stT120 (i+1)) + stT120 64 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 63
    simpa using h
  have hprev := st120_p63
  have hstep := st120_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p65 : ((107032634911/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT120 (i+1))
      = (∑ i ∈ Finset.range 64, stT120 (i+1)) + stT120 65 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 64
    simpa using h
  have hprev := st120_p64
  have hstep := st120_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p66 : ((14297716468967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT120 (i+1))
      = (∑ i ∈ Finset.range 65, stT120 (i+1)) + stT120 66 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 65
    simpa using h
  have hprev := st120_p65
  have hstep := st120_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p67 : ((2860506477343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT120 (i+1))
      = (∑ i ∈ Finset.range 66, stT120 (i+1)) + stT120 67 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 66
    simpa using h
  have hprev := st120_p66
  have hstep := st120_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p68 : ((27416276762409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT120 (i+1))
      = (∑ i ∈ Finset.range 67, stT120 (i+1)) + stT120 68 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 67
    simpa using h
  have hprev := st120_p67
  have hstep := st120_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p69 : ((27862908080409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT120 (i+1))
      = (∑ i ∈ Finset.range 68, stT120 (i+1)) + stT120 69 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 68
    simpa using h
  have hprev := st120_p68
  have hstep := st120_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p70 : ((5778091986949/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT120 (i+1))
      = (∑ i ∈ Finset.range 69, stT120 (i+1)) + stT120 70 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 69
    simpa using h
  have hprev := st120_p69
  have hstep := st120_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p71 : ((28155891721589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT120 (i+1))
      = (∑ i ∈ Finset.range 70, stT120 (i+1)) + stT120 71 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 70
    simpa using h
  have hprev := st120_p70
  have hstep := st120_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p72 : ((27313800114133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT120 (i+1))
      = (∑ i ∈ Finset.range 71, stT120 (i+1)) + stT120 72 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 71
    simpa using h
  have hprev := st120_p71
  have hstep := st120_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p73 : ((28200199180873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT120 (i+1))
      = (∑ i ∈ Finset.range 72, stT120 (i+1)) + stT120 73 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 72
    simpa using h
  have hprev := st120_p72
  have hstep := st120_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p74 : ((28903292565097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT120 (i+1))
      = (∑ i ∈ Finset.range 73, stT120 (i+1)) + stT120 74 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 73
    simpa using h
  have hprev := st120_p73
  have hstep := st120_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p75 : ((13978274875547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT120 (i+1))
      = (∑ i ∈ Finset.range 74, stT120 (i+1)) + stT120 75 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 74
    simpa using h
  have hprev := st120_p74
  have hstep := st120_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p76 : ((3414667497293/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT120 (i+1))
      = (∑ i ∈ Finset.range 75, stT120 (i+1)) + stT120 76 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 75
    simpa using h
  have hprev := st120_p75
  have hstep := st120_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p77 : ((14131110335997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT120 (i+1))
      = (∑ i ∈ Finset.range 76, stT120 (i+1)) + stT120 77 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 76
    simpa using h
  have hprev := st120_p76
  have hstep := st120_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p78 : ((1156637767791/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT120 (i+1))
      = (∑ i ∈ Finset.range 77, stT120 (i+1)) + stT120 78 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 77
    simpa using h
  have hprev := st120_p77
  have hstep := st120_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p79 : ((28025464044887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT120 (i+1))
      = (∑ i ∈ Finset.range 78, stT120 (i+1)) + stT120 79 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 78
    simpa using h
  have hprev := st120_p78
  have hstep := st120_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p80 : ((5457806811133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT120 (i+1))
      = (∑ i ∈ Finset.range 79, stT120 (i+1)) + stT120 80 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 79
    simpa using h
  have hprev := st120_p79
  have hstep := st120_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p81 : ((28063818422631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT120 (i+1))
      = (∑ i ∈ Finset.range 80, stT120 (i+1)) + stT120 81 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 80
    simpa using h
  have hprev := st120_p80
  have hstep := st120_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p82 : ((28927070292651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT120 (i+1))
      = (∑ i ∈ Finset.range 81, stT120 (i+1)) + stT120 82 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 81
    simpa using h
  have hprev := st120_p81
  have hstep := st120_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p83 : ((14173338643521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT120 (i+1))
      = (∑ i ∈ Finset.range 82, stT120 (i+1)) + stT120 83 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 82
    simpa using h
  have hprev := st120_p82
  have hstep := st120_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p84 : ((6837973086473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT120 (i+1))
      = (∑ i ∈ Finset.range 83, stT120 (i+1)) + stT120 84 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 83
    simpa using h
  have hprev := st120_p83
  have hstep := st120_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p85 : ((86387632117/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT120 (i+1))
      = (∑ i ∈ Finset.range 84, stT120 (i+1)) + stT120 85 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 84
    simpa using h
  have hprev := st120_p84
  have hstep := st120_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p86 : ((2871631986297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT120 (i+1))
      = (∑ i ∈ Finset.range 85, stT120 (i+1)) + stT120 86 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 85
    simpa using h
  have hprev := st120_p85
  have hstep := st120_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p87 : ((14399903148261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT120 (i+1))
      = (∑ i ∈ Finset.range 86, stT120 (i+1)) + stT120 87 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 86
    simpa using h
  have hprev := st120_p86
  have hstep := st120_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p88 : ((13887243702593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT120 (i+1))
      = (∑ i ∈ Finset.range 87, stT120 (i+1)) + stT120 88 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 87
    simpa using h
  have hprev := st120_p87
  have hstep := st120_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p89 : ((13636756635211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT120 (i+1))
      = (∑ i ∈ Finset.range 88, stT120 (i+1)) + stT120 89 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 88
    simpa using h
  have hprev := st120_p88
  have hstep := st120_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p90 : ((14032199776057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT120 (i+1))
      = (∑ i ∈ Finset.range 89, stT120 (i+1)) + stT120 90 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 89
    simpa using h
  have hprev := st120_p89
  have hstep := st120_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p91 : ((14463645690931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT120 (i+1))
      = (∑ i ∈ Finset.range 90, stT120 (i+1)) + stT120 91 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 90
    simpa using h
  have hprev := st120_p90
  have hstep := st120_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p92 : ((28575165478831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT120 (i+1))
      = (∑ i ∈ Finset.range 91, stT120 (i+1)) + stT120 92 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 91
    simpa using h
  have hprev := st120_p91
  have hstep := st120_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p93 : ((27540772676367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT120 (i+1))
      = (∑ i ∈ Finset.range 92, stT120 (i+1)) + stT120 93 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 92
    simpa using h
  have hprev := st120_p92
  have hstep := st120_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p94 : ((27319280990399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT120 (i+1))
      = (∑ i ∈ Finset.range 93, stT120 (i+1)) + stT120 94 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 93
    simpa using h
  have hprev := st120_p93
  have hstep := st120_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p95 : ((5642191078453/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT120 (i+1))
      = (∑ i ∈ Finset.range 94, stT120 (i+1)) + stT120 95 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 94
    simpa using h
  have hprev := st120_p94
  have hstep := st120_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p96 : ((5793025446393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT120 (i+1))
      = (∑ i ∈ Finset.range 95, stT120 (i+1)) + stT120 96 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 95
    simpa using h
  have hprev := st120_p95
  have hstep := st120_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p97 : ((7139628566229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT120 (i+1))
      = (∑ i ∈ Finset.range 96, stT120 (i+1)) + stT120 97 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 96
    simpa using h
  have hprev := st120_p96
  have hstep := st120_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p98 : ((2755092503323/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT120 (i+1))
      = (∑ i ∈ Finset.range 97, stT120 (i+1)) + stT120 98 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 97
    simpa using h
  have hprev := st120_p97
  have hstep := st120_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p99 : ((2727258980951/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT120 (i+1))
      = (∑ i ∈ Finset.range 98, stT120 (i+1)) + stT120 99 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 98
    simpa using h
  have hprev := st120_p98
  have hstep := st120_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st120_p100 : ((3508931376331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT120 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT120 (i+1))
      = (∑ i ∈ Finset.range 99, stT120 (i+1)) + stT120 100 := by
    have h := Finset.sum_range_succ (fun i => stT120 (i+1)) 99
    simpa using h
  have hprev := st120_p99
  have hstep := st120_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 120`.** -/
theorem station_120_sign : hardyG (((120:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 120 100 (by norm_num) (by norm_num)
    ((345427/1000000 : ℚ) : ℝ)
  have hchain := st120_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT120 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((120:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((345427/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((120:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((120:ℕ)):ℝ)+1) * ((((120:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((552781/400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((3508931376331/1250000000000 : ℚ) : ℝ) - ((552781/400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((345427/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((120:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((345427/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((120:ℕ)):ℝ))).re
      - Real.sin ((345427/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((120:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((120:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((120:ℕ)):ℝ)
      = ((((120:ℕ)):ℝ) * (Real.log (((120:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((120:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_120
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
  have hθwin : |(((345427/1000000 : ℚ) : ℝ) + ((19:ℤ)) * (2*Real.pi) - Real.pi) - theta (((120:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((120:ℕ)):ℝ))
    (φ := ((345427/1000000 : ℚ) : ℝ) + ((19:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((345427/1000000 : ℚ) : ℝ) + ((19:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((345427/1000000 : ℚ)) : ℝ) - Real.pi) + ((19:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((345427/1000000 : ℚ)) : ℝ) - Real.pi) 19).1,
    (cos_sin_shift ((((345427/1000000 : ℚ)) : ℝ) - Real.pi) 19).2]
  exact cos_sin_flip ((345427/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_120_sign
end AxiomAudit
