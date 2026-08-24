import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table
import RequestProject.DVPLog500Table

/-!
# The cosine table at `t = 813/2` (rung-406.5; halved brackets, N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos813o2_br_2 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (2 : ℕ) / 2)) - ((278917/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (2 : ℕ) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -611889/2500000) (δ := 10189/500000000) 813 45
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_3 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (3 : ℕ) / 2)) - ((887123/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (3 : ℕ) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1199307/10000000) (δ := 10171/500000000) 813 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_4 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (4 : ℕ) / 2)) - ((-377623/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (4 : ℕ) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4895061/10000000) (δ := 4071/200000000) 813 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_5 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (5 : ℕ) / 2)) - ((88401/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (5 : ℕ) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1963137/10000000) (δ := 10199/500000000) 813 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_6 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (6 : ℕ) / 2)) - ((109741/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (6 : ℕ) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -624099/5000000) (δ := 10167/500000000) 813 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_7 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (7 : ℕ) / 2)) - ((784521/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (7 : ℕ) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -836091/5000000) (δ := 20397/1000000000) 813 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_8 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (8 : ℕ) / 2)) - ((-979149/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (8 : ℕ) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3671283/5000000) (δ := 5083/250000000) 813 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_9 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (9 : ℕ) / 2)) - ((573957/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (9 : ℕ) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 479733/2000000) (δ := 20371/1000000000) 813 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_10 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (10 : ℕ) / 2)) - ((490641/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (10 : ℕ) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -48447/1000000) (δ := 10191/500000000) 813 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_11 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (11 : ℕ) / 2)) - ((32973/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (11 : ℕ) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2126741/10000000) (δ := 20439/1000000000) 813 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_12 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (12 : ℕ) / 2)) - ((92383/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (12 : ℕ) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3695703/10000000) (δ := 20357/1000000000) 813 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_13 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (13 : ℕ) / 2)) - ((468501/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (13 : ℕ) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -446063/5000000) (δ := 2051/100000000) 813 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_14 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (14 : ℕ) / 2)) - ((-38501/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (14 : ℕ) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4119687/10000000) (δ := 10187/500000000) 813 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_15 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (15 : ℕ) / 2)) - ((60211/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (15 : ℕ) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 632499/2000000) (δ := 10229/500000000) 813 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_16 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (16 : ℕ) / 2)) - ((-11169/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (16 : ℕ) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1479473/2500000) (δ := 319/15625000) 813 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_17 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (17 : ℕ) / 2)) - ((-60539/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (17 : ℕ) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4695789/10000000) (δ := 4073/200000000) 813 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_18 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (18 : ℕ) / 2)) - ((999809/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (18 : ℕ) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1221/250000) (δ := 10197/500000000) 813 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_19 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (19 : ℕ) / 2)) - ((-249869/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (19 : ℕ) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3886531/5000000) (δ := 20337/1000000000) 813 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_20 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (20 : ℕ) / 2)) - ((387581/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (20 : ℕ) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -117279/400000) (δ := 20359/1000000000) 813 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_21 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (21 : ℕ) / 2)) - ((122771/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (21 : ℕ) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59103/1250000) (δ := 20337/1000000000) 813 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_22 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (22 : ℕ) / 2)) - ((49589/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (22 : ℕ) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -80191/2500000) (δ := 319/15625000) 813 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_23 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (23 : ℕ) / 2)) - ((307581/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (23 : ℕ) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -141907/625000) (δ := 10197/500000000) 813 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_24 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (24 : ℕ) / 2)) - ((-96857/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (24 : ℕ) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -767901/1250000) (δ := 1019/50000000) 813 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_25 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (25 : ℕ) / 2)) - ((307/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (25 : ℕ) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3926223/10000000) (δ := 4079/200000000) 813 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_26 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (26 : ℕ) / 2)) - ((58197/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (26 : ℕ) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3339631/10000000) (δ := 20487/1000000000) 813 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_27 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (27 : ℕ) / 2)) - ((16401/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log (27 : ℕ) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (27 : ℕ) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3598023/10000000) (δ := 20431/1000000000) 813 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_28 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (28 : ℕ) / 2)) - ((-870433/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (28 : ℕ) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -820899/1250000) (δ := 20351/1000000000) 813 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_29 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (29 : ℕ) / 2)) - ((37433/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (29 : ℕ) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -464317/2000000) (δ := 10193/500000000) 813 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_30 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (30 : ℕ) / 2)) - ((959393/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (30 : ℕ) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 89361/1250000) (δ := 20331/1000000000) 813 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_31 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (31 : ℕ) / 2)) - ((498717/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log (31 : ℕ) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (31 : ℕ) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2621697/10000000) (δ := 10229/500000000) 813 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_32 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (32 : ℕ) / 2)) - ((45407/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (32 : ℕ) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3470387/10000000) (δ := 20393/1000000000) 813 224
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_33 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (33 : ℕ) / 2)) - ((238049/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (33 : ℕ) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3326099/10000000) (δ := 20379/1000000000) 813 226
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_34 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (34 : ℕ) / 2)) - ((622147/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (34 : ℕ) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 562071/2500000) (δ := 5097/250000000) 813 228
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_35 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (35 : ℕ) / 2)) - ((496619/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (35 : ℕ) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36363/1250000) (δ := 51/2500000) 813 230
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_36 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (36 : ℕ) / 2)) - ((135383/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (36 : ℕ) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -499269/2000000) (δ := 20417/1000000000) 813 232
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_37 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (37 : ℕ) / 2)) - ((-755501/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (37 : ℕ) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3034019/5000000) (δ := 5083/250000000) 813 234
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_38 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (38 : ℕ) / 2)) - ((-5307/10000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (38 : ℕ) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5325557/10000000) (δ := 20339/1000000000) 813 235
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_39 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (39 : ℕ) / 2)) - ((496229/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log (39 : ℕ) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (39 : ℕ) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9601/312500) (δ := 409/20000000) 813 237
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_40 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (40 : ℕ) / 2)) - ((-548857/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (40 : ℕ) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -134487/250000) (δ := 1271/62500000) 813 239
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_41 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (41 : ℕ) / 2)) - ((-31763/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (41 : ℕ) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1001603/2500000) (δ := 821/40000000) 813 240
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_42 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (42 : ℕ) / 2)) - ((391871/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (42 : ℕ) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2920329/10000000) (δ := 20339/1000000000) 813 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_43 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (43 : ℕ) / 2)) - ((-516737/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (43 : ℕ) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2642289/5000000) (δ := 20457/1000000000) 813 243
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_44 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (44 : ℕ) / 2)) - ((447071/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (44 : ℕ) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2768269/10000000) (δ := 20393/1000000000) 813 245
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_45 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (45 : ℕ) / 2)) - ((-173029/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log (45 : ℕ) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (45 : ℕ) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4361751/10000000) (δ := 1273/62500000) 813 246
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_46 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (46 : ℕ) / 2)) - ((-77799/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (46 : ℕ) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4718119/10000000) (δ := 20521/1000000000) 813 248
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_47 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (47 : ℕ) / 2)) - ((420443/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (47 : ℕ) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22339/156250) (δ := 20489/1000000000) 813 249
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_48 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (48 : ℕ) / 2)) - ((-956891/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (48 : ℕ) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28469/40000) (δ := 20357/1000000000) 813 250
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_49 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (49 : ℕ) / 2)) - ((230927/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (49 : ℕ) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1672207/5000000) (δ := 20511/1000000000) 813 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_50 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (50 : ℕ) / 2)) - ((25941/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (50 : ℕ) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 739359/5000000) (δ := 10209/500000000) 813 253
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_51 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (51 : ℕ) / 2)) - ((-88553/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (51 : ℕ) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5895147/10000000) (δ := 817/40000000) 813 254
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_52 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (52 : ℕ) / 2)) - ((-677279/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (52 : ℕ) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45212/78125) (δ := 1279/62500000) 813 256
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_53 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (53 : ℕ) / 2)) - ((656259/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (53 : ℕ) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1068683/5000000) (δ := 2557/125000000) 813 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_54 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (54 : ℕ) / 2)) - ((22399/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (54 : ℕ) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 575259/5000000) (δ := 10227/500000000) 813 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_55 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (55 : ℕ) / 2)) - ((-1017/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (55 : ℕ) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4089827/10000000) (δ := 10221/500000000) 813 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_56 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (56 : ℕ) / 2)) - ((-894123/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (56 : ℕ) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1338633/2000000) (δ := 5117/250000000) 813 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_57 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (57 : ℕ) / 2)) - ((-450793/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (57 : ℕ) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6735543/10000000) (δ := 20483/1000000000) 813 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_58 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (58 : ℕ) / 2)) - ((-165253/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (58 : ℕ) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -476909/1000000) (δ := 20363/1000000000) 813 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_59 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (59 : ℕ) / 2)) - ((161477/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (59 : ℕ) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3104869/10000000) (δ := 20397/1000000000) 813 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_60 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (60 : ℕ) / 2)) - ((769303/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (60 : ℕ) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1732617/10000000) (δ := 10177/500000000) 813 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_61 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (61 : ℕ) / 2)) - ((967139/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (61 : ℕ) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -642679/10000000) (δ := 20411/1000000000) 813 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_62 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (62 : ℕ) / 2)) - ((124697/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (62 : ℕ) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 174091/10000000) (δ := 5117/250000000) 813 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_63 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (63 : ℕ) / 2)) - ((239517/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (63 : ℕ) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 363267/5000000) (δ := 2547/125000000) 813 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_64 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (64 : ℕ) / 2)) - ((458737/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (64 : ℕ) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51139/500000) (δ := 513/25000000) 813 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_65 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (65 : ℕ) / 2)) - ((454819/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (65 : ℕ) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13387/125000) (δ := 20513/1000000000) 813 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_66 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (66 : ℕ) / 2)) - ((938879/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (66 : ℕ) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 439297/5000000) (δ := 5089/250000000) 813 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_67 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (67 : ℕ) / 2)) - ((245909/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (67 : ℕ) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 452897/10000000) (δ := 10227/500000000) 813 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_68 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (68 : ℕ) / 2)) - ((996827/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (68 : ℕ) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -199221/10000000) (δ := 5103/250000000) 813 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_69 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (69 : ℕ) / 2)) - ((454803/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (69 : ℕ) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -535577/5000000) (δ := 10167/500000000) 813 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_70 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (70 : ℕ) / 2)) - ((325217/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (70 : ℕ) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2156601/10000000) (δ := 20377/1000000000) 813 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_71 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (71 : ℕ) / 2)) - ((189851/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (71 : ℕ) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -431183/1250000) (δ := 20483/1000000000) 813 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_72 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (72 : ℕ) / 2)) - ((-395621/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (72 : ℕ) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -98877/200000) (δ := 511/25000000) 813 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_73 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (73 : ℕ) / 2)) - ((-441673/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (73 : ℕ) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1658593/2500000) (δ := 20497/1000000000) 813 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_74 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (74 : ℕ) / 2)) - ((-48259/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (74 : ℕ) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7192319/10000000) (δ := 20497/1000000000) 813 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_75 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (75 : ℕ) / 2)) - ((-461279/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (75 : ℕ) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5125581/10000000) (δ := 4091/200000000) 813 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_76 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (76 : ℕ) / 2)) - ((407373/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (76 : ℕ) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 719513/2500000) (δ := 10181/500000000) 813 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_77 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (77 : ℕ) / 2)) - ((122939/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (77 : ℕ) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45461/1000000) (δ := 10217/500000000) 813 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_78 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (78 : ℕ) / 2)) - ((655381/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (78 : ℕ) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2140273/10000000) (δ := 20427/1000000000) 813 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_79 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (79 : ℕ) / 2)) - ((-95069/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (79 : ℕ) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4902227/10000000) (δ := 20433/1000000000) 813 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_80 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (80 : ℕ) / 2)) - ((-499971/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (80 : ℕ) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1565397/2000000) (δ := 20341/1000000000) 813 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_81 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (81 : ℕ) / 2)) - ((-68233/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (81 : ℕ) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4797381/10000000) (δ := 20491/1000000000) 813 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_82 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (82 : ℕ) / 2)) - ((811803/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (82 : ℕ) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 779453/5000000) (δ := 4101/200000000) 813 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_83 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (83 : ℕ) / 2)) - ((92957/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (83 : ℕ) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -457671/2500000) (δ := 4071/200000000) 813 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_84 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (84 : ℕ) / 2)) - ((-272487/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (84 : ℕ) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1073577/2000000) (δ := 40691/1000000000) 813 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_85 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (85 : ℕ) / 2)) - ((-887897/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (85 : ℕ) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53271/80000) (δ := 10181/500000000) 813 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_86 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (86 : ℕ) / 2)) - ((105581/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (86 : ℕ) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 709243/2500000) (δ := 20469/1000000000) 813 288
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_87 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (87 : ℕ) / 2)) - ((900929/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (87 : ℕ) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1122227/10000000) (δ := 20327/1000000000) 813 289
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_88 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (88 : ℕ) / 2)) - ((-492981/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (88 : ℕ) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2607887/5000000) (δ := 20369/1000000000) 813 290
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_89 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (89 : ℕ) / 2)) - ((-201319/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (89 : ℕ) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6267343/10000000) (δ := 10167/500000000) 813 290
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_90 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (90 : ℕ) / 2)) - ((720899/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (90 : ℕ) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 957123/5000000) (δ := 20391/1000000000) 813 291
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_91 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (91 : ℕ) / 2)) - ((518481/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (91 : ℕ) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2564307/10000000) (δ := 20399/500000000) 813 292
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_92 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (92 : ℕ) / 2)) - ((-240583/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (92 : ℕ) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -895703/1250000) (δ := 10249/500000000) 813 293
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_93 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (93 : ℕ) / 2)) - ((21201/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (93 : ℕ) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1910477/5000000) (δ := 4101/200000000) 813 293
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_94 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (94 : ℕ) / 2)) - ((918247/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (94 : ℕ) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1017911/10000000) (δ := 10181/500000000) 813 294
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_95 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (95 : ℕ) / 2)) - ((-182433/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (95 : ℕ) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1194363/2000000) (δ := 20419/1000000000) 813 295
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_96 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (96 : ℕ) / 2)) - ((-292711/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (96 : ℕ) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4669643/10000000) (δ := 5121/250000000) 813 295
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_97 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (97 : ℕ) / 2)) - ((122437/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (97 : ℕ) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -126781/2500000) (δ := 20477/1000000000) 813 296
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_98 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (98 : ℕ) / 2)) - ((-339343/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (98 : ℕ) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -72399/125000) (δ := 20519/1000000000) 813 297
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_99 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (99 : ℕ) / 2)) - ((-237107/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (99 : ℕ) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4525457/10000000) (δ := 10167/500000000) 813 297
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_100 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (100 : ℕ) / 2)) - ((231459/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (100 : ℕ) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -968889/10000000) (δ := 10181/500000000) 813 298
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_101 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (101 : ℕ) / 2)) - ((-869953/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (101 : ℕ) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3282379/5000000) (δ := 10199/500000000) 813 299
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_102 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (102 : ℕ) / 2)) - ((190567/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (102 : ℕ) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1723821/5000000) (δ := 639/31250000) 813 299
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_103 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (103 : ℕ) / 2)) - ((591181/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (103 : ℕ) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -469137/2000000) (δ := 5087/250000000) 813 300
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_104 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (104 : ℕ) / 2)) - ((-123553/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (104 : ℕ) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7473221/10000000) (δ := 4071/200000000) 813 300
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_105 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (105 : ℕ) / 2)) - ((827529/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (105 : ℕ) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 745131/5000000) (δ := 1017/50000000) 813 301
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_106 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (106 : ℕ) / 2)) - ((-65041/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (106 : ℕ) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1146243/2500000) (δ := 2047/100000000) 813 302
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_107 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (107 : ℕ) / 2)) - ((-400597/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log (107 : ℕ) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (107 : ℕ) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1239353/2500000) (δ := 2037/100000000) 813 302
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_108 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (108 : ℕ) / 2)) - ((868417/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log (108 : ℕ) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (108 : ℕ) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1296987/10000000) (δ := 20477/1000000000) 813 303
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_109 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (109 : ℕ) / 2)) - ((-996291/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (109 : ℕ) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7638581/10000000) (δ := 20369/1000000000) 813 304
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_110 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (110 : ℕ) / 2)) - ((12373/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (110 : ℕ) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 821161/5000000) (δ := 20419/1000000000) 813 304
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_111 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (111 : ℕ) / 2)) - ((-367831/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (111 : ℕ) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -121717/250000) (δ := 20391/1000000000) 813 305
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_112 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (112 : ℕ) / 2)) - ((-127123/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (112 : ℕ) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 212283/500000) (δ := 20491/1000000000) 813 305
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_113 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (113 : ℕ) / 2)) - ((282013/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (113 : ℕ) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2428857/10000000) (δ := 10249/500000000) 813 306
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_114 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (114 : ℕ) / 2)) - ((-26937/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log (114 : ℕ) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (114 : ℕ) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1304983/2000000) (δ := 10199/500000000) 813 306
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_115 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (115 : ℕ) / 2)) - ((992449/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (115 : ℕ) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -153713/5000000) (δ := 20397/1000000000) 813 307
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_116 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (116 : ℕ) / 2)) - ((-193537/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (116 : ℕ) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7216697/10000000) (δ := 2049/100000000) 813 308
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_117 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (117 : ℕ) / 2)) - ((205961/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (117 : ℕ) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 150659/1000000) (δ := 2039/100000000) 813 308
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_118 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (118 : ℕ) / 2)) - ((-151327/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (118 : ℕ) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2776187/5000000) (δ := 1021/50000000) 813 309
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_119 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (119 : ℕ) / 2)) - ((8839/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (119 : ℕ) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 755889/2500000) (δ := 20433/1000000000) 813 309
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_120 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (120 : ℕ) / 2)) - ((-2527/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (120 : ℕ) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2090061/5000000) (δ := 20377/1000000000) 813 310
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_121 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (121 : ℕ) / 2)) - ((-65123/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (121 : ℕ) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4253533/10000000) (δ := 5119/250000000) 813 310
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_122 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (122 : ℕ) / 2)) - ((328507/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (122 : ℕ) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -386273/1250000) (δ := 10217/500000000) 813 311
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_123 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (123 : ℕ) / 2)) - ((-61187/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (123 : ℕ) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5205769/10000000) (δ := 20469/1000000000) 813 311
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_124 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (124 : ℕ) / 2)) - ((307123/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (124 : ℕ) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1136707/5000000) (δ := 5123/250000000) 813 312
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_125 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (125 : ℕ) / 2)) - ((-353387/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (125 : ℕ) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5889309/10000000) (δ := 2549/125000000) 813 312
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_126 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (126 : ℕ) / 2)) - ((772271/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (126 : ℕ) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1720971/10000000) (δ := 20399/1000000000) 813 313
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_127 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (127 : ℕ) / 2)) - ((-407937/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (127 : ℕ) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6312587/10000000) (δ := 20449/1000000000) 813 313
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_128 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (128 : ℕ) / 2)) - ((21049/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (128 : ℕ) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56989/400000) (δ := 20497/1000000000) 813 314
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_129 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (129 : ℕ) / 2)) - ((-853559/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (129 : ℕ) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 202623/312500) (δ := 20397/1000000000) 813 314
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_130 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (130 : ℕ) / 2)) - ((852201/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (130 : ℕ) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -275309/2000000) (δ := 2049/100000000) 813 315
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_131 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (131 : ℕ) / 2)) - ((-837971/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (131 : ℕ) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3205439/5000000) (δ := 20513/1000000000) 813 315
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_132 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (132 : ℕ) / 2)) - ((40473/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (132 : ℕ) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1568911/10000000) (δ := 20333/1000000000) 813 316
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_133 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (133 : ℕ) / 2)) - ((-95507/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (133 : ℕ) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6100931/10000000) (δ := 20333/1000000000) 813 316
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_134 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (134 : ℕ) / 2)) - ((349119/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (134 : ℕ) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1994659/10000000) (δ := 40727/1000000000) 813 317
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_135 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (135 : ℕ) / 2)) - ((-304043/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (135 : ℕ) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5561109/10000000) (δ := 20427/1000000000) 813 317
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_136 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (136 : ℕ) / 2)) - ((489979/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (136 : ℕ) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -661707/2500000) (δ := 1273/62500000) 813 318
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_137 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (137 : ℕ) / 2)) - ((-341519/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (137 : ℕ) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4798321/10000000) (δ := 10209/500000000) 813 318
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_138 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (138 : ℕ) / 2)) - ((162567/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (138 : ℕ) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3518761/10000000) (δ := 20461/1000000000) 813 319
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_139 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (139 : ℕ) / 2)) - ((8647/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (139 : ℕ) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3818869/10000000) (δ := 20411/1000000000) 813 319
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_140 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (140 : ℕ) / 2)) - ((-267547/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (140 : ℕ) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2302053/5000000) (δ := 10177/500000000) 813 320
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_141 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (141 : ℕ) / 2)) - ((496199/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (141 : ℕ) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 328619/1250000) (δ := 20399/1000000000) 813 320
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_142 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (142 : ℕ) / 2)) - ((-354469/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (142 : ℕ) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5896969/10000000) (δ := 10253/500000000) 813 321
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_143 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (143 : ℕ) / 2)) - ((440253/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (143 : ℕ) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1234667/10000000) (δ := 10253/500000000) 813 321
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_144 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (144 : ℕ) / 2)) - ((-491467/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (144 : ℕ) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7391457/10000000) (δ := 1017/50000000) 813 322
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_145 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (145 : ℕ) / 2)) - ((123717/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (145 : ℕ) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -358499/10000000) (δ := 2039/100000000) 813 322
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_146 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (146 : ℕ) / 2)) - ((-881787/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (146 : ℕ) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3313043/5000000) (δ := 20413/1000000000) 813 322
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_147 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (147 : ℕ) / 2)) - ((130787/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (147 : ℕ) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2145057/10000000) (δ := 10241/500000000) 813 323
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_148 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (148 : ℕ) / 2)) - ((-160663/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (148 : ℕ) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2372407/5000000) (δ := 20521/1000000000) 813 323
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_149 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (149 : ℕ) / 2)) - ((-4811/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (149 : ℕ) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4119621/10000000) (δ := 819/40000000) 813 324
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_150 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (150 : ℕ) / 2)) - ((11977/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (150 : ℕ) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1338987/5000000) (δ := 2541/125000000) 813 324
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_151 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (151 : ℕ) / 2)) - ((-403829/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (151 : ℕ) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1255483/2000000) (δ := 10259/500000000) 813 325
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_152 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (152 : ℕ) / 2)) - ((985207/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (152 : ℕ) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 430547/10000000) (δ := 4077/200000000) 813 325
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_153 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (153 : ℕ) / 2)) - ((-954209/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (153 : ℕ) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1418901/2000000) (δ := 4097/200000000) 813 325
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_154 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (154 : ℕ) / 2)) - ((698743/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (154 : ℕ) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -398579/2000000) (δ := 20411/1000000000) 813 326
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_155 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (155 : ℕ) / 2)) - ((-260091/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (155 : ℕ) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4584783/10000000) (δ := 20461/1000000000) 813 326
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_156 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (156 : ℕ) / 2)) - ((-4082/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (156 : ℕ) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2293889/5000000) (δ := 5101/250000000) 813 327
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_157 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (157 : ℕ) / 2)) - ((36161/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (157 : ℕ) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29779/156250) (δ := 2563/125000000) 813 327
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_158 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (158 : ℕ) / 2)) - ((-979727/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (158 : ℕ) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1837433/2500000) (δ := 2557/125000000) 813 328
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_159 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (159 : ℕ) / 2)) - ((930433/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (159 : ℕ) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -117251/1250000) (δ := 20397/1000000000) 813 328
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_160 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (160 : ℕ) / 2)) - ((-566781/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (160 : ℕ) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5433473/10000000) (δ := 20397/1000000000) 813 328
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_161 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (161 : ℕ) / 2)) - ((-6301/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (161 : ℕ) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -492843/1250000) (δ := 10257/500000000) 813 329
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_162 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (162 : ℕ) / 2)) - ((147457/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (162 : ℕ) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 587469/2500000) (δ := 10257/500000000) 813 329
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_163 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (163 : ℕ) / 2)) - ((-955361/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (163 : ℕ) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7104187/10000000) (δ := 10191/500000000) 813 330
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_164 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (164 : ℕ) / 2)) - ((468747/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (164 : ℕ) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -888599/10000000) (δ := 10241/500000000) 813 330
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_165 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (165 : ℕ) / 2)) - ((-518313/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (165 : ℕ) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1057837/2000000) (δ := 10191/500000000) 813 330
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_166 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (166 : ℕ) / 2)) - ((-70029/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (166 : ℕ) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4278291/10000000) (δ := 817/40000000) 813 331
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_167 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (167 : ℕ) / 2)) - ((372533/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (167 : ℕ) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14261/78125) (δ := 819/40000000) 813 331
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_168 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (168 : ℕ) / 2)) - ((-999881/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (168 : ℕ) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7815441/10000000) (δ := 10209/500000000) 813 332
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_169 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (169 : ℕ) / 2)) - ((377979/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (169 : ℕ) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8921/50000) (δ := 4087/200000000) 813 332
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_170 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (170 : ℕ) / 2)) - ((-113507/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log (170 : ℕ) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (170 : ℕ) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 421137/1000000) (δ := 4077/200000000) 813 332
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_171 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (171 : ℕ) / 2)) - ((-300071/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (171 : ℕ) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2768093/5000000) (δ := 20511/1000000000) 813 333
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_172 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (172 : ℕ) / 2)) - ((98789/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (172 : ℕ) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 389467/10000000) (δ := 5123/250000000) 813 333
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_173 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (173 : ℕ) / 2)) - ((-808449/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (173 : ℕ) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6280769/10000000) (δ := 20511/1000000000) 813 333
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_174 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (174 : ℕ) / 2)) - ((142377/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (174 : ℕ) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1784917/5000000) (δ := 10227/500000000) 813 334
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_175 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (175 : ℕ) / 2)) - ((620359/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (175 : ℕ) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 225399/1000000) (δ := 5101/250000000) 813 334
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_176 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (176 : ℕ) / 2)) - ((-199419/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (176 : ℕ) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7663381/10000000) (δ := 1281/62500000) 813 335
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_177 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (177 : ℕ) / 2)) - ((180829/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (177 : ℕ) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1905511/10000000) (δ := 20457/1000000000) 813 335
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_178 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (178 : ℕ) / 2)) - ((1339/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (178 : ℕ) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1909919/5000000) (δ := 20357/1000000000) 813 335
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_179 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (179 : ℕ) / 2)) - ((-196933/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (179 : ℕ) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1548697/2500000) (δ := 20339/1000000000) 813 336
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_180 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (180 : ℕ) / 2)) - ((977337/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log (180 : ℕ) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (180 : ℕ) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -533259/10000000) (δ := 10207/500000000) 813 336
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_181 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (181 : ℕ) / 2)) - ((-225547/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (181 : ℕ) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5096969/10000000) (δ := 20339/1000000000) 813 336
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_182 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (182 : ℕ) / 2)) - ((-420457/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (182 : ℕ) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5011863/10000000) (δ := 20421/1000000000) 813 337
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_183 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (183 : ℕ) / 2)) - ((975311/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (183 : ℕ) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 556679/10000000) (δ := 20471/1000000000) 813 337
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_184 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (184 : ℕ) / 2)) - ((-9531/12500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (184 : ℕ) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1218967/2000000) (δ := 20471/1000000000) 813 337
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_185 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (185 : ℕ) / 2)) - ((-17781/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (185 : ℕ) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -513119/1250000) (δ := 2541/125000000) 813 338
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_186 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (186 : ℕ) / 2)) - ((852849/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (186 : ℕ) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 171681/1250000) (δ := 821/40000000) 813 338
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_187 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (187 : ℕ) / 2)) - ((-916097/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (187 : ℕ) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6822581/10000000) (δ := 2541/125000000) 813 338
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_188 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (188 : ℕ) / 2)) - ((183583/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (188 : ℕ) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -433177/1250000) (δ := 4077/200000000) 813 339
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_189 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (189 : ℕ) / 2)) - ((358831/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (189 : ℕ) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 481473/2500000) (δ := 4087/200000000) 813 339
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_190 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (190 : ℕ) / 2)) - ((-48727/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log (190 : ℕ) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (190 : ℕ) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7288643/10000000) (δ := 4067/200000000) 813 339
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_191 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (191 : ℕ) / 2)) - ((330609/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (191 : ℕ) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1542309/5000000) (δ := 2051/100000000) 813 340
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_192 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (192 : ℕ) / 2)) - ((630301/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (192 : ℕ) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1111069/5000000) (δ := 1023/50000000) 813 340
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_193 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (193 : ℕ) / 2)) - ((-990069/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (193 : ℕ) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3750677/5000000) (δ := 20393/1000000000) 813 340
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_194 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (194 : ℕ) / 2)) - ((94803/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (194 : ℕ) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2954629/10000000) (δ := 41/2000000) 813 341
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_195 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (195 : ℕ) / 2)) - ((615223/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (195 : ℕ) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1135159/5000000) (δ := 20453/1000000000) 813 341
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_196 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (196 : ℕ) / 2)) - ((-494069/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (196 : ℕ) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7468539/10000000) (δ := 409/20000000) 813 341
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_197 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (197 : ℕ) / 2)) - ((42127/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (197 : ℕ) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3067627/10000000) (δ := 10223/500000000) 813 342
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_198 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (198 : ℕ) / 2)) - ((168501/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (198 : ℕ) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16234/78125) (δ := 20357/1000000000) 813 342
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_199 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (199 : ℕ) / 2)) - ((-241433/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (199 : ℕ) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 449851/625000) (δ := 5099/250000000) 813 342
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_200 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (200 : ℕ) / 2)) - ((101411/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (200 : ℕ) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1708197/5000000) (δ := 20339/1000000000) 813 343
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_201 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (201 : ℕ) / 2)) - ((789439/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (201 : ℕ) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 330451/2000000) (δ := 10257/500000000) 813 343
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_202 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (202 : ℕ) / 2)) - ((-894559/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (202 : ℕ) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3347799/5000000) (δ := 20489/1000000000) 813 343
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_203 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (203 : ℕ) / 2)) - ((-26727/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (203 : ℕ) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3993817/10000000) (δ := 20521/1000000000) 813 344
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_204 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (204 : ℕ) / 2)) - ((28783/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (204 : ℕ) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 200007/2000000) (δ := 5083/250000000) 813 344
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_205 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (205 : ℕ) / 2)) - ((-364549/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (205 : ℕ) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2984749/5000000) (δ := 20521/1000000000) 813 344
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_206 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (206 : ℕ) / 2)) - ((-339589/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (206 : ℕ) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -479319/1000000) (δ := 2541/125000000) 813 345
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_207 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (207 : ℕ) / 2)) - ((998687/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (207 : ℕ) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64051/5000000) (δ := 817/40000000) 813 345
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_208 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (208 : ℕ) / 2)) - ((-212739/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (208 : ℕ) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1256429/2500000) (δ := 10189/500000000) 813 345
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_209 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (209 : ℕ) / 2)) - ((-683427/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (209 : ℕ) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5808109/10000000) (δ := 10193/500000000) 813 346
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_210 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (210 : ℕ) / 2)) - ((463793/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (210 : ℕ) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -957243/10000000) (δ := 1271/62500000) 813 346
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_211 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (211 : ℕ) / 2)) - ((22573/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (211 : ℕ) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1935277/5000000) (δ := 20417/1000000000) 813 346
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_212 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (212 : ℕ) / 2)) - ((-473247/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (212 : ℕ) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7032477/10000000) (δ := 20493/1000000000) 813 347
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_213 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (213 : ℕ) / 2)) - ((77697/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (213 : ℕ) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2250107/10000000) (δ := 2051/100000000) 813 347
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_214 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (214 : ℕ) / 2)) - ((536963/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (214 : ℕ) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2509907/10000000) (δ := 20393/1000000000) 813 347
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_215 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (215 : ℕ) / 2)) - ((-485367/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (215 : ℕ) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 452979/625000) (δ := 1023/50000000) 813 347
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_216 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (216 : ℕ) / 2)) - ((14587/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (216 : ℕ) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -936123/2500000) (δ := 41/2000000) 813 348
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_217 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (217 : ℕ) / 2)) - ((116093/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (217 : ℕ) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 189893/2000000) (δ := 409/20000000) 813 348
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_218 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (218 : ℕ) / 2)) - ((-627201/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (218 : ℕ) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5621877/10000000) (δ := 20453/1000000000) 813 348
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_219 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (219 : ℕ) / 2)) - ((-567289/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (219 : ℕ) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1087003/2000000) (δ := 1281/62500000) 813 349
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_220 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (220 : ℕ) / 2)) - ((948581/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (220 : ℕ) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -805183/10000000) (δ := 5099/250000000) 813 349
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_221 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (221 : ℕ) / 2)) - ((49291/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (221 : ℕ) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1901857/5000000) (δ := 5099/250000000) 813 349
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_222 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (222 : ℕ) / 2)) - ((-3053/3125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (222 : ℕ) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7316287/10000000) (δ := 20389/1000000000) 813 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_223 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (223 : ℕ) / 2)) - ((90801/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (223 : ℕ) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2748853/10000000) (δ := 20389/1000000000) 813 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_224 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (224 : ℕ) / 2)) - ((188073/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (224 : ℕ) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 359631/2000000) (δ := 10257/500000000) 813 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_225 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (225 : ℕ) / 2)) - ((-818721/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (225 : ℕ) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6324939/10000000) (δ := 10257/500000000) 813 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_226 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (226 : ℕ) / 2)) - ((-185353/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (226 : ℕ) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4876413/10000000) (δ := 10193/250000000) 813 351
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_227 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (227 : ℕ) / 2)) - ((24697/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (227 : ℕ) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -389619/10000000) (δ := 20431/1000000000) 813 351
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_228 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (228 : ℕ) / 2)) - ((-60131/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (228 : ℕ) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 407741/1000000) (δ := 10211/500000000) 813 351
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_229 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (229 : ℕ) / 2)) - ((-482101/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (229 : ℕ) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7183037/10000000) (δ := 20329/1000000000) 813 352
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_230 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (230 : ℕ) / 2)) - ((451837/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (230 : ℕ) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2754931/10000000) (δ := 10187/500000000) 813 352
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_231 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (231 : ℕ) / 2)) - ((394509/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (231 : ℕ) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 103373/625000) (δ := 10187/500000000) 813 352
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_232 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (232 : ℕ) / 2)) - ((-46819/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (232 : ℕ) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3021881/5000000) (δ := 20479/1000000000) 813 352
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_233 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (233 : ℕ) / 2)) - ((-519689/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (233 : ℕ) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5293209/10000000) (δ := 20417/1000000000) 813 353
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_234 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (234 : ℕ) / 2)) - ((465003/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (234 : ℕ) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -188183/2000000) (δ := 20367/1000000000) 813 353
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_235 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (235 : ℕ) / 2)) - ((212061/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (235 : ℕ) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1696391/5000000) (δ := 10243/500000000) 813 353
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_236 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (236 : ℕ) / 2)) - ((-499149/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (236 : ℕ) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1927021/2500000) (δ := 1271/62500000) 813 353
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_237 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (237 : ℕ) / 2)) - ((89529/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (237 : ℕ) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3702869/10000000) (δ := 20493/1000000000) 813 354
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_238 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (238 : ℕ) / 2)) - ((97357/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (238 : ℕ) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 576051/10000000) (δ := 2041/100000000) 813 354
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_239 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (239 : ℕ) / 2)) - ((-356051/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (239 : ℕ) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2418543/5000000) (δ := 20393/1000000000) 813 354
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_240 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (240 : ℕ) / 2)) - ((-441039/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (240 : ℕ) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6627627/10000000) (δ := 51/2500000) 813 355
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_241 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (241 : ℕ) / 2)) - ((114569/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (241 : ℕ) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -120103/500000) (δ := 20453/1000000000) 813 355
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_242 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (242 : ℕ) / 2)) - ((375107/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (242 : ℕ) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 451507/2500000) (δ := 20453/1000000000) 813 355
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_243 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (243 : ℕ) / 2)) - ((-11508/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (243 : ℕ) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2998369/5000000) (δ := 20503/1000000000) 813 355
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_244 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (244 : ℕ) / 2)) - ((-300311/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (244 : ℕ) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5537689/10000000) (δ := 20457/1000000000) 813 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_245 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (245 : ℕ) / 2)) - ((851209/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (245 : ℕ) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -690639/5000000) (δ := 10199/250000000) 813 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_246 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (246 : ℕ) / 2)) - ((56331/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (246 : ℕ) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 344783/1250000) (δ := 10223/500000000) 813 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_247 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (247 : ℕ) / 2)) - ((-462607/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (247 : ℕ) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6880987/10000000) (δ := 10223/500000000) 813 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_248 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (248 : ℕ) / 2)) - ((-15613/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (248 : ℕ) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4720919/10000000) (δ := 4103/200000000) 813 357
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_249 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (249 : ℕ) / 2)) - ((968273/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log (249 : ℕ) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (249 : ℕ) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -157857/2500000) (δ := 5097/250000000) 813 357
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_250 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (250 : ℕ) / 2)) - ((192859/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (250 : ℕ) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 860451/2500000) (δ := 4083/200000000) 813 357
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_251 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (251 : ℕ) / 2)) - ((-494959/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log (251 : ℕ) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (251 : ℕ) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3749337/5000000) (δ := 4083/200000000) 813 357
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_252 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (252 : ℕ) / 2)) - ((-19297/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log (252 : ℕ) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (252 : ℕ) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2084289/5000000) (δ := 20381/1000000000) 813 358
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_253 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (253 : ℕ) / 2)) - ((499173/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log (253 : ℕ) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (253 : ℕ) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -143821/10000000) (δ := 2559/125000000) 813 358
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_254 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (254 : ℕ) / 2)) - ((24761/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log (254 : ℕ) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (254 : ℕ) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1932541/5000000) (δ := 2559/125000000) 813 358
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_255 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (255 : ℕ) / 2)) - ((-999999/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log (255 : ℕ) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (255 : ℕ) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7849731/10000000) (δ := 5131/250000000) 813 359
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_256 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (256 : ℕ) / 2)) - ((21903/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log (256 : ℕ) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (256 : ℕ) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -387223/1000000) (δ := 10237/500000000) 813 359
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_257 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (257 : ℕ) / 2)) - ((249839/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log (257 : ℕ) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (257 : ℕ) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 89723/10000000) (δ := 20479/1000000000) 813 359
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_258 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (258 : ℕ) / 2)) - ((-43721/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log (258 : ℕ) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (258 : ℕ) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4036329/10000000) (δ := 5131/250000000) 813 359
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_259 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (259 : ℕ) / 2)) - ((-499483/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log (259 : ℕ) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (259 : ℕ) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7740271/10000000) (δ := 20467/1000000000) 813 360
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_260 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (260 : ℕ) / 2)) - ((8233/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log (260 : ℕ) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (260 : ℕ) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76481/200000) (δ := 20467/1000000000) 813 360
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_261 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (261 : ℕ) / 2)) - ((249881/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log (261 : ℕ) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (261 : ℕ) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77131/10000000) (δ := 10193/500000000) 813 360
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_262 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (262 : ℕ) / 2)) - ((-1819/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log (262 : ℕ) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (262 : ℕ) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 990843/2500000) (δ := 61167/1000000000) 813 360
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_263 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (263 : ℕ) / 2)) - ((-99997/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log (263 : ℕ) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (263 : ℕ) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7834777/10000000) (δ := 10193/500000000) 813 360
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_264 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (264 : ℕ) / 2)) - ((-17881/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log (264 : ℕ) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (264 : ℕ) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -125513/312500) (δ := 60993/1000000000) 813 361
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_265 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (265 : ℕ) / 2)) - ((997571/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log (265 : ℕ) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (265 : ℕ) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4357/250000) (δ := 1023/50000000) 813 361
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_266 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (266 : ℕ) / 2)) - ((13651/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log (266 : ℕ) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (266 : ℕ) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1826713/5000000) (δ := 20343/1000000000) 813 361
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_267 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (267 : ℕ) / 2)) - ((-39521/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log (267 : ℕ) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (267 : ℕ) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7466701/10000000) (δ := 20393/1000000000) 813 361
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_268 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (268 : ℕ) / 2)) - ((-102317/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log (268 : ℕ) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (268 : ℕ) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -888443/2000000) (δ := 20351/1000000000) 813 362
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_269 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (269 : ℕ) / 2)) - ((241409/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log (269 : ℕ) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (269 : ℕ) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -328647/5000000) (δ := 10251/500000000) 813 362
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_270 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (270 : ℕ) / 2)) - ((63929/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log (270 : ℕ) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (270 : ℕ) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 778401/2500000) (δ := 20451/1000000000) 813 362
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_271 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (271 : ℕ) / 2)) - ((-461813/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log (271 : ℕ) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (271 : ℕ) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3435289/5000000) (δ := 5113/250000000) 813 362
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_272 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (272 : ℕ) / 2)) - ((-450153/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log (272 : ℕ) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (272 : ℕ) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5094333/10000000) (δ := 4069/200000000) 813 363
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_273 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (273 : ℕ) / 2)) - ((53413/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log (273 : ℕ) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (273 : ℕ) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -273/2000) (δ := 10229/500000000) 813 363
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_274 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (274 : ℕ) / 2)) - ((147381/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log (274 : ℕ) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (274 : ℕ) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73463/312500) (δ := 4079/200000000) 813 363
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_275 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (275 : ℕ) / 2)) - ((-187881/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log (275 : ℕ) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (275 : ℕ) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6052913/10000000) (δ := 4089/200000000) 813 363
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_276 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (276 : ℕ) / 2)) - ((-182053/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log (276 : ℕ) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (276 : ℕ) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2983133/5000000) (δ := 10219/500000000) 813 364
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_277 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (277 : ℕ) / 2)) - ((304373/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log (277 : ℕ) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (277 : ℕ) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1145397/5000000) (δ := 4093/200000000) 813 364
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_278 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (278 : ℕ) / 2)) - ((213321/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log (278 : ℕ) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (278 : ℕ) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 342841/2500000) (δ := 5097/250000000) 813 364
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_279 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (279 : ℕ) / 2)) - ((-423521/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log (279 : ℕ) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (279 : ℕ) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5020311/10000000) (δ := 2561/125000000) 813 364
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_280 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (280 : ℕ) / 2)) - ((-948937/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log (280 : ℕ) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (280 : ℕ) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7051611/10000000) (δ := 20331/1000000000) 813 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_281 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (281 : ℕ) / 2)) - ((198007/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (281 : ℕ) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -85717/250000) (δ := 20431/1000000000) 813 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_282 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (282 : ℕ) / 2)) - ((997367/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log (282 : ℕ) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (282 : ℕ) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 181447/10000000) (δ := 10211/500000000) 813 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_283 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (283 : ℕ) / 2)) - ((29627/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log (283 : ℕ) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (283 : ℕ) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3778769/10000000) (δ := 10261/500000000) 813 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_284 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (284 : ℕ) / 2)) - ((-196163/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log (284 : ℕ) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (284 : ℕ) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7363489/10000000) (δ := 10211/500000000) 813 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_285 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (285 : ℕ) / 2)) - ((-331777/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log (285 : ℕ) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (285 : ℕ) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4772457/10000000) (δ := 20479/1000000000) 813 366
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_286 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (286 : ℕ) / 2)) - ((221153/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log (286 : ℕ) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (286 : ℕ) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1212839/10000000) (δ := 5131/250000000) 813 366
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_287 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (287 : ℕ) / 2)) - ((297427/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log (287 : ℕ) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (287 : ℕ) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58357/250000) (δ := 5131/250000000) 813 366
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_288 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (288 : ℕ) / 2)) - ((-175251/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log (288 : ℕ) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (288 : ℕ) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5869001/10000000) (δ := 2553/125000000) 813 366
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_289 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (289 : ℕ) / 2)) - ((-816763/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log (289 : ℕ) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (289 : ℕ) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1579109/2500000) (δ := 5109/250000000) 813 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_290 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (290 : ℕ) / 2)) - ((5419/12500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log (290 : ℕ) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (290 : ℕ) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -701501/2500000) (δ := 20367/1000000000) 813 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_291 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (291 : ℕ) / 2)) - ((961909/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log (291 : ℕ) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (291 : ℕ) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 692233/10000000) (δ := 20517/1000000000) 813 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_292 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (292 : ℕ) / 2)) - ((-50233/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log (292 : ℕ) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (292 : ℕ) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4178581/10000000) (δ := 5109/250000000) 813 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_293 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (293 : ℕ) / 2)) - ((-31149/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log (293 : ℕ) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (293 : ℕ) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 956617/1250000) (δ := 20417/1000000000) 813 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_294 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (294 : ℕ) / 2)) - ((-52619/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log (294 : ℕ) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (294 : ℕ) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2296281/5000000) (δ := 20459/1000000000) 813 368
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_295 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (295 : ℕ) / 2)) - ((897507/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log (295 : ℕ) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (295 : ℕ) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1141783/10000000) (δ := 10197/500000000) 813 368
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_296 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (296 : ℕ) / 2)) - ((606677/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log (296 : ℕ) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (296 : ℕ) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 574327/2500000) (δ := 20509/1000000000) 813 368
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_297 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (297 : ℕ) / 2)) - ((-65873/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log (297 : ℕ) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (297 : ℕ) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1144963/2000000) (δ := 10197/500000000) 813 368
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_298 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (298 : ℕ) / 2)) - ((-21761/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log (298 : ℕ) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (298 : ℕ) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6567227/10000000) (δ := 20451/1000000000) 813 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_299 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (299 : ℕ) / 2)) - ((300981/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log (299 : ℕ) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (299 : ℕ) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49417/156250) (δ := 20401/1000000000) 813 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_300 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (300 : ℕ) / 2)) - ((497877/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log (300 : ℕ) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (300 : ℕ) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 230469/10000000) (δ := 20351/1000000000) 813 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_301 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (301 : ℕ) / 2)) - ((62763/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log (301 : ℕ) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (301 : ℕ) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1806173/5000000) (δ := 20451/1000000000) 813 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_302 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (302 : ℕ) / 2)) - ((-939929/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log (302 : ℕ) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (302 : ℕ) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1745761/2500000) (δ := 20451/1000000000) 813 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_303 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (303 : ℕ) / 2)) - ((-27207/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log (303 : ℕ) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (303 : ℕ) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26827/50000) (δ := 10229/500000000) 813 370
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_304 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (304 : ℕ) / 2)) - ((27673/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log (304 : ℕ) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (304 : ℕ) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1008479/5000000) (δ := 2551/125000000) 813 370
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_305 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (305 : ℕ) / 2)) - ((431867/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log (305 : ℕ) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (305 : ℕ) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1320407/10000000) (δ := 2551/125000000) 813 370
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_306 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (306 : ℕ) / 2)) - ((-284039/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log (306 : ℕ) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (306 : ℕ) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4647/10000) (δ := 5127/250000000) 813 370
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_307 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (307 : ℕ) / 2)) - ((-62441/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log (307 : ℕ) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (307 : ℕ) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3872673/5000000) (δ := 4103/200000000) 813 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_308 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (308 : ℕ) / 2)) - ((-203963/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log (308 : ℕ) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (308 : ℕ) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4440501/10000000) (δ := 4103/200000000) 813 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_309 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (309 : ℕ) / 2)) - ((14011/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log (309 : ℕ) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (309 : ℕ) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1146327/10000000) (δ := 4073/200000000) 813 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_310 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (310 : ℕ) / 2)) - ((164079/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log (310 : ℕ) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (310 : ℕ) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2137177/10000000) (δ := 4093/200000000) 813 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_311 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (311 : ℕ) / 2)) - ((-559091/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log (311 : ℕ) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (311 : ℕ) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5410213/10000000) (δ := 10169/500000000) 813 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_312 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (312 : ℕ) / 2)) - ((-946869/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log (312 : ℕ) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (312 : ℕ) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -879423/1250000) (δ := 10261/500000000) 813 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_313 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (313 : ℕ) / 2)) - ((57411/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log (313 : ℕ) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (313 : ℕ) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -472923/1250000) (δ := 10261/500000000) 813 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_314 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (314 : ℕ) / 2)) - ((244153/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log (314 : ℕ) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (314 : ℕ) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2167/40000) (δ := 10211/500000000) 813 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_315 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (315 : ℕ) / 2)) - ((237493/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log (315 : ℕ) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (315 : ℕ) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 134481/500000) (δ := 5093/250000000) 813 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_316 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (316 : ℕ) / 2)) - ((-89101/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log (316 : ℕ) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (316 : ℕ) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2955363/5000000) (δ := 5093/250000000) 813 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_317 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (317 : ℕ) / 2)) - ((-218547/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log (317 : ℕ) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (317 : ℕ) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1646599/2500000) (δ := 5131/250000000) 813 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_318 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (318 : ℕ) / 2)) - ((107431/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log (318 : ℕ) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (318 : ℕ) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -677123/2000000) (δ := 5131/250000000) 813 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_319 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (319 : ℕ) / 2)) - ((498483/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log (319 : ℕ) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (319 : ℕ) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -194793/10000000) (δ := 2553/125000000) 813 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_320 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (320 : ℕ) / 2)) - ((367621/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log (320 : ℕ) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (320 : ℕ) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1492933/5000000) (δ := 5131/250000000) 813 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_321 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (321 : ℕ) / 2)) - ((-389137/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log (321 : ℕ) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (321 : ℕ) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 615677/1000000) (δ := 20429/1000000000) 813 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_322 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (322 : ℕ) / 2)) - ((-5209/6250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log (322 : ℕ) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (322 : ℕ) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25561/40000) (δ := 5129/250000000) 813 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_323 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (323 : ℕ) / 2)) - ((8491/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log (323 : ℕ) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (323 : ℕ) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1619531/5000000) (δ := 5129/250000000) 813 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_324 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (324 : ℕ) / 2)) - ((499619/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log (324 : ℕ) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (324 : ℕ) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9763/1000000) (δ := 5129/250000000) 813 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_325 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (325 : ℕ) / 2)) - ((5463/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log (325 : ℕ) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (325 : ℕ) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1517023/5000000) (δ := 5129/250000000) 813 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_326 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (326 : ℕ) / 2)) - ((-778123/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log (326 : ℕ) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (326 : ℕ) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 615617/1000000) (δ := 20437/1000000000) 813 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_327 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (327 : ℕ) / 2)) - ((-168821/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log (327 : ℕ) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (327 : ℕ) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6439223/10000000) (δ := 2543/125000000) 813 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_328 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (328 : ℕ) / 2)) - ((2927/12500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log (328 : ℕ) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (328 : ℕ) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -417013/1250000) (δ := 20459/1000000000) 813 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_329 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (329 : ℕ) / 2)) - ((497649/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log (329 : ℕ) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (329 : ℕ) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -242537/10000000) (δ := 2543/125000000) 813 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_330 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (330 : ℕ) / 2)) - ((52577/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log (330 : ℕ) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (330 : ℕ) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35521/125000) (δ := 20359/1000000000) 813 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_331 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (331 : ℕ) / 2)) - ((-17861/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log (331 : ℕ) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (331 : ℕ) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1479137/2500000) (δ := 5111/250000000) 813 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_332 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (332 : ℕ) / 2)) - ((-224973/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log (332 : ℕ) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (332 : ℕ) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1681449/2500000) (δ := 10201/500000000) 813 376
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_333 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (333 : ℕ) / 2)) - ((20569/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log (333 : ℕ) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (333 : ℕ) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -229339/625000) (δ := 159/7812500) 813 376
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_334 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (334 : ℕ) / 2)) - ((969189/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log (334 : ℕ) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (334 : ℕ) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -311099/5000000) (δ := 20451/1000000000) 813 376
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_335 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (335 : ℕ) / 2)) - ((568271/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log (335 : ℕ) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (335 : ℕ) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2415983/10000000) (δ := 20451/1000000000) 813 376
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_336 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (336 : ℕ) / 2)) - ((-570579/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log (336 : ℕ) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (336 : ℕ) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5445017/10000000) (δ := 10251/500000000) 813 376
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_337 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (337 : ℕ) / 2)) - ((-97027/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log (337 : ℕ) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (337 : ℕ) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3621427/5000000) (δ := 10179/500000000) 813 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_338 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (338 : ℕ) / 2)) - ((-973/8000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log (338 : ℕ) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (338 : ℕ) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4231807/10000000) (δ := 4069/200000000) 813 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_339 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (339 : ℕ) / 2)) - ((220371/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log (339 : ℕ) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (339 : ℕ) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2459/20000) (δ := 4099/200000000) 813 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_340 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (340 : ℕ) / 2)) - ((380629/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log (340 : ℕ) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (340 : ℕ) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 352773/2000000) (δ := 2551/125000000) 813 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_341 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (341 : ℕ) / 2)) - ((-322679/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log (341 : ℕ) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (341 : ℕ) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1187097/2500000) (δ := 2551/125000000) 813 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_342 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (342 : ℕ) / 2)) - ((-499327/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log (342 : ℕ) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (342 : ℕ) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7724273/10000000) (δ := 10229/500000000) 813 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_343 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (343 : ℕ) / 2)) - ((-84431/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log (343 : ℕ) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (343 : ℕ) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1003309/2000000) (δ := 4103/200000000) 813 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_344 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (344 : ℕ) / 2)) - ((679867/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log (344 : ℕ) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (344 : ℕ) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1029019/5000000) (δ := 4103/200000000) 813 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_345 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (345 : ℕ) / 2)) - ((937029/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log (345 : ℕ) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (345 : ℕ) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 222983/2500000) (δ := 10169/500000000) 813 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_346 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (346 : ℕ) / 2)) - ((18741/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log (346 : ℕ) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (346 : ℕ) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 239579/625000) (δ := 2561/125000000) 813 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_347 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (347 : ℕ) / 2)) - ((-14169/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log (347 : ℕ) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (347 : ℕ) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3383081/5000000) (δ := 4073/200000000) 813 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_348 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (348 : ℕ) / 2)) - ((-742061/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log (348 : ℕ) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (348 : ℕ) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6017339/10000000) (δ := 2043/100000000) 813 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_349 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (349 : ℕ) / 2)) - ((324339/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log (349 : ℕ) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (349 : ℕ) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3101209/10000000) (δ := 20473/1000000000) 813 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_350 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (350 : ℕ) / 2)) - ((498503/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log (350 : ℕ) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (350 : ℕ) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38703/2000000) (δ := 1019/50000000) 813 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_351 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (351 : ℕ) / 2)) - ((469229/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log (351 : ℕ) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (351 : ℕ) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 676487/2500000) (δ := 2033/100000000) 813 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_352 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (352 : ℕ) / 2)) - ((-154861/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log (352 : ℕ) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (352 : ℕ) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2798539/5000000) (δ := 20473/1000000000) 813 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_353 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (353 : ℕ) / 2)) - ((-242201/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log (353 : ℕ) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (353 : ℕ) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3613943/5000000) (δ := 2033/100000000) 813 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_354 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (354 : ℕ) / 2)) - ((-84793/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log (354 : ℕ) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (354 : ℕ) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -544127/1250000) (δ := 8/390625) 813 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_355 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (355 : ℕ) / 2)) - ((2071/2500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log (355 : ℕ) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (355 : ℕ) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -743189/5000000) (δ := 8/390625) 813 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_356 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (356 : ℕ) / 2)) - ((426541/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log (356 : ℕ) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (356 : ℕ) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1372333/10000000) (δ := 1019/50000000) 813 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_357 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (357 : ℕ) / 2)) - ((-118093/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log (357 : ℕ) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (357 : ℕ) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2111457/5000000) (δ := 20373/1000000000) 813 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_358 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (358 : ℕ) / 2)) - ((-950683/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log (358 : ℕ) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (358 : ℕ) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7065569/10000000) (δ := 8/390625) 813 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_359 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (359 : ℕ) / 2)) - ((-341649/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log (359 : ℕ) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (359 : ℕ) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5807667/10000000) (δ := 10183/500000000) 813 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_360 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (360 : ℕ) / 2)) - ((184759/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log (360 : ℕ) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (360 : ℕ) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -745191/2500000) (δ := 20437/1000000000) 813 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_361 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (361 : ℕ) / 2)) - ((997907/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log (361 : ℕ) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (361 : ℕ) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40447/2500000) (δ := 20487/1000000000) 813 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_362 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (362 : ℕ) / 2)) - ((489059/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log (362 : ℕ) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (362 : ℕ) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 331183/1250000) (δ := 20337/1000000000) 813 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_363 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (363 : ℕ) / 2)) - ((-573163/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log (363 : ℕ) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (363 : ℕ) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5452891/10000000) (δ := 319/15625000) 813 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_364 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (364 : ℕ) / 2)) - ((-61723/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log (364 : ℕ) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (364 : ℕ) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -932421/1250000) (δ := 5111/250000000) 813 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_365 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (365 : ℕ) / 2)) - ((-293339/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log (365 : ℕ) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (365 : ℕ) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2335643/5000000) (δ := 10247/500000000) 813 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_366 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (366 : ℕ) / 2)) - ((727359/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log (366 : ℕ) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (366 : ℕ) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -945413/5000000) (δ := 10247/500000000) 813 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_367 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (367 : ℕ) / 2)) - ((938407/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log (367 : ℕ) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (367 : ℕ) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 220503/2500000) (δ := 5111/250000000) 813 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_368 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (368 : ℕ) / 2)) - ((111631/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log (368 : ℕ) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (368 : ℕ) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 364733/1000000) (δ := 10247/500000000) 813 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_369 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (369 : ℕ) / 2)) - ((-418357/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log (369 : ℕ) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (369 : ℕ) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6405127/10000000) (δ := 20409/1000000000) 813 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_370 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (370 : ℕ) / 2)) - ((-216879/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log (370 : ℕ) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (370 : ℕ) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6552457/10000000) (δ := 20351/1000000000) 813 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_371 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (371 : ℕ) / 2)) - ((2347/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log (371 : ℕ) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (371 : ℕ) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1904799/5000000) (δ := 20451/1000000000) 813 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_372 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (372 : ℕ) / 2)) - ((909123/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log (372 : ℕ) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (372 : ℕ) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1074057/10000000) (δ := 10251/500000000) 813 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_373 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (373 : ℕ) / 2)) - ((788969/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log (373 : ℕ) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (373 : ℕ) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 206771/1250000) (δ := 10201/500000000) 813 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_374 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (374 : ℕ) / 2)) - ((-44559/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log (374 : ℕ) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (374 : ℕ) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2187487/5000000) (δ := 5113/250000000) 813 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_375 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (375 : ℕ) / 2)) - ((-238377/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log (375 : ℕ) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (375 : ℕ) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7088667/10000000) (δ := 20451/1000000000) 813 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_376 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (376 : ℕ) / 2)) - ((-44589/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log (376 : ℕ) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (376 : ℕ) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5912921/10000000) (δ := 2551/125000000) 813 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_377 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (377 : ℕ) / 2)) - ((140719/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log (377 : ℕ) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (377 : ℕ) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3213761/10000000) (δ := 2551/125000000) 813 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_378 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (378 : ℕ) / 2)) - ((15286/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log (378 : ℕ) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (378 : ℕ) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -104343/2000000) (δ := 4069/200000000) 813 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_379 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (379 : ℕ) / 2)) - ((648391/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log (379 : ℕ) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (379 : ℕ) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2163319/10000000) (δ := 4079/200000000) 813 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_380 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (380 : ℕ) / 2)) - ((-71513/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log (380 : ℕ) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (380 : ℕ) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2420569/5000000) (δ := 10179/500000000) 813 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_381 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (381 : ℕ) / 2)) - ((-198131/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log (381 : ℕ) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (381 : ℕ) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1502389/2000000) (δ := 5127/250000000) 813 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_382 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (382 : ℕ) / 2)) - ((-598841/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log (382 : ℕ) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (382 : ℕ) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5532123/10000000) (δ := 20487/1000000000) 813 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_383 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (383 : ℕ) / 2)) - ((408363/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log (383 : ℕ) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (383 : ℕ) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -143767/500000) (δ := 319/15625000) 813 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_384 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (384 : ℕ) / 2)) - ((49797/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log (384 : ℕ) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (384 : ℕ) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -225367/10000000) (δ := 20437/1000000000) 813 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_385 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (385 : ℕ) / 2)) - ((567707/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log (385 : ℕ) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (385 : ℕ) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75553/312500) (δ := 20437/1000000000) 813 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_386 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (386 : ℕ) / 2)) - ((-87127/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log (386 : ℕ) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (386 : ℕ) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5053849/10000000) (δ := 319/15625000) 813 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_387 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (387 : ℕ) / 2)) - ((-997667/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log (387 : ℕ) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (387 : ℕ) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 960399/1250000) (δ := 20487/1000000000) 813 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_388 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (388 : ℕ) / 2)) - ((-556409/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log (388 : ℕ) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (388 : ℕ) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2701067/5000000) (δ := 20523/1000000000) 813 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_389 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (389 : ℕ) / 2)) - ((220303/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log (389 : ℕ) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (389 : ℕ) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2786307/10000000) (δ := 2033/100000000) 813 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_390 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (390 : ℕ) / 2)) - ((997489/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log (390 : ℕ) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (390 : ℕ) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -177187/10000000) (δ := 2043/100000000) 813 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_391 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (391 : ℕ) / 2)) - ((22609/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log (391 : ℕ) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (391 : ℕ) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1212613/5000000) (δ := 2043/100000000) 813 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_392 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (392 : ℕ) / 2)) - ((-211891/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log (392 : ℕ) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (392 : ℕ) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2510517/5000000) (δ := 20473/1000000000) 813 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_393 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (393 : ℕ) / 2)) - ((-995251/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log (393 : ℕ) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (393 : ℕ) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1522047/2000000) (δ := 8/390625) 813 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_394 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (394 : ℕ) / 2)) - ((-74173/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log (394 : ℕ) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (394 : ℕ) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1378783/2500000) (δ := 20423/1000000000) 813 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_395 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (395 : ℕ) / 2)) - ((384937/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log (395 : ℕ) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (395 : ℕ) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2939141/10000000) (δ := 2043/100000000) 813 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_396 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (396 : ℕ) / 2)) - ((494547/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log (396 : ℕ) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (396 : ℕ) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -369553/10000000) (δ := 1019/50000000) 813 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_397 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (397 : ℕ) / 2)) - ((25567/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log (397 : ℕ) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (397 : ℕ) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2193429/10000000) (δ := 20473/1000000000) 813 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_398 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (398 : ℕ) / 2)) - ((-80833/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log (398 : ℕ) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (398 : ℕ) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4750111/10000000) (δ := 20373/1000000000) 813 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_399 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (399 : ℕ) / 2)) - ((-487787/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log (399 : ℕ) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (399 : ℕ) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7300289/10000000) (δ := 1019/50000000) 813 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_400 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (400 : ℕ) / 2)) - ((-699547/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log (400 : ℕ) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (400 : ℕ) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5863899/10000000) (δ := 20337/1000000000) 813 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_401 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (401 : ℕ) / 2)) - ((237923/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log (401 : ℕ) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (401 : ℕ) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -415803/1250000) (δ := 20487/1000000000) 813 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_402 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (402 : ℕ) / 2)) - ((949819/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log (402 : ℕ) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (402 : ℕ) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -99419/1250000) (δ := 20387/1000000000) 813 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_403 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (403 : ℕ) / 2)) - ((385047/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log (403 : ℕ) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (403 : ℕ) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1729521/10000000) (δ := 20337/1000000000) 813 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_404 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (404 : ℕ) / 2)) - ((-16011/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log (404 : ℕ) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (404 : ℕ) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4248093/10000000) (δ := 10233/500000000) 813 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_405 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (405 : ℕ) / 2)) - ((-452927/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log (405 : ℕ) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (405 : ℕ) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6760467/10000000) (δ := 20487/1000000000) 813 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_406 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (406 : ℕ) / 2)) - ((-168911/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log (406 : ℕ) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (406 : ℕ) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6441323/10000000) (δ := 20509/1000000000) 813 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_407 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (407 : ℕ) / 2)) - ((-5743/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log (407 : ℕ) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (407 : ℕ) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -985337/2500000) (δ := 20509/1000000000) 813 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_408 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (408 : ℕ) / 2)) - ((837017/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log (408 : ℕ) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (408 : ℕ) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -144747/1000000) (δ := 2543/125000000) 813 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_409 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (409 : ℕ) / 2)) - ((914663/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log (409 : ℕ) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (409 : ℕ) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 104031/1000000) (δ := 2543/125000000) 813 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_410 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (410 : ℕ) / 2)) - ((40323/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log (410 : ℕ) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (410 : ℕ) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 440249/1250000) (δ := 20509/1000000000) 813 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_411 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (411 : ℕ) / 2)) - ((-368383/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log (411 : ℕ) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (411 : ℕ) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5997679/10000000) (δ := 20359/1000000000) 813 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_412 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (412 : ℕ) / 2)) - ((-970061/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log (412 : ℕ) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (412 : ℕ) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1448139/2000000) (δ := 159/7812500) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_413 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (413 : ℕ) / 2)) - ((-333529/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log (413 : ℕ) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (413 : ℕ) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2388551/5000000) (δ := 20401/1000000000) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_414 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (414 : ℕ) / 2)) - ((599627/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log (414 : ℕ) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (414 : ℕ) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2319403/10000000) (δ := 20401/1000000000) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_415 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (415 : ℕ) / 2)) - ((499299/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log (415 : ℕ) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (415 : ℕ) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66201/5000000) (δ := 159/7812500) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_416 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (416 : ℕ) / 2)) - ((513717/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log (416 : ℕ) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (416 : ℕ) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2578211/10000000) (δ := 10201/500000000) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_417 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (417 : ℕ) / 2)) - ((-84553/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log (417 : ℕ) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (417 : ℕ) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5018227/10000000) (δ := 20351/1000000000) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_418 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (418 : ℕ) / 2)) - ((-987123/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log (418 : ℕ) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (418 : ℕ) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7452349/10000000) (δ := 20351/1000000000) 813 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_419 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (419 : ℕ) / 2)) - ((-689007/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log (419 : ℕ) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (419 : ℕ) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1165457/2000000) (δ := 10197/500000000) 813 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_420 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (420 : ℕ) / 2)) - ((207381/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log (420 : ℕ) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (420 : ℕ) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -851187/2500000) (δ := 20359/1000000000) 813 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_421 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (421 : ℕ) / 2)) - ((922919/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log (421 : ℕ) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (421 : ℕ) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -247001/2500000) (δ := 2543/125000000) 813 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_422 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (422 : ℕ) / 2)) - ((421161/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log (422 : ℕ) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (422 : ℕ) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1423049/10000000) (δ := 10197/500000000) 813 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_423 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (423 : ℕ) / 2)) - ((19731/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log (423 : ℕ) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (423 : ℕ) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 382831/1000000) (δ := 20459/1000000000) 813 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_424 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (424 : ℕ) / 2)) - ((-397921/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log (424 : ℕ) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (424 : ℕ) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6227981/10000000) (δ := 20409/1000000000) 813 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_425 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (425 : ℕ) / 2)) - ((-476593/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log (425 : ℕ) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (425 : ℕ) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3543001/5000000) (δ := 10233/500000000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_426 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (426 : ℕ) / 2)) - ((-30339/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log (426 : ℕ) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (426 : ℕ) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1174403/2500000) (δ := 20487/1000000000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_427 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (427 : ℕ) / 2)) - ((75137/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log (427 : ℕ) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (427 : ℕ) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -231481/1000000) (δ := 319/15625000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_428 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (428 : ℕ) / 2)) - ((99969/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log (428 : ℕ) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (428 : ℕ) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 623/100000) (δ := 20387/1000000000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_429 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (429 : ℕ) / 2)) - ((281159/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log (429 : ℕ) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (429 : ℕ) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 304253/1250000) (δ := 20487/1000000000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_430 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (430 : ℕ) / 2)) - ((-342209/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log (430 : ℕ) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (430 : ℕ) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4800159/10000000) (δ := 20437/1000000000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_431 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (431 : ℕ) / 2)) - ((-192359/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log (431 : ℕ) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (431 : ℕ) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1432141/2000000) (δ := 319/15625000) 813 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_432 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (432 : ℕ) / 2)) - ((-787069/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log (432 : ℕ) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (432 : ℕ) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6192099/10000000) (δ := 20373/1000000000) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_433 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (433 : ℕ) / 2)) - ((33859/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log (433 : ℕ) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (433 : ℕ) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1921163/5000000) (δ := 1019/50000000) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_434 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (434 : ℕ) / 2)) - ((412889/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log (434 : ℕ) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (434 : ℕ) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37451/250000) (δ := 20473/1000000000) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_435 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (435 : ℕ) / 2)) - ((29499/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log (435 : ℕ) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (435 : ℕ) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 840859/10000000) (δ := 2033/100000000) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_436 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (436 : ℕ) / 2)) - ((296521/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log (436 : ℕ) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (436 : ℕ) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 793593/2500000) (δ := 2043/100000000) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_437 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (437 : ℕ) / 2)) - ((-589309/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log (437 : ℕ) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (437 : ℕ) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5502499/10000000) (δ := 8/390625) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_438 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (438 : ℕ) / 2)) - ((-199987/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log (438 : ℕ) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (438 : ℕ) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1956361/2500000) (δ := 20473/1000000000) 813 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_439 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (439 : ℕ) / 2)) - ((-609309/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log (439 : ℕ) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (439 : ℕ) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2782481/5000000) (δ := 20523/1000000000) 813 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_440 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (440 : ℕ) / 2)) - ((266463/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log (440 : ℕ) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (440 : ℕ) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -203293/625000) (δ := 20373/1000000000) 813 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_441 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (441 : ℕ) / 2)) - ((929301/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log (441 : ℕ) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (441 : ℕ) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -945699/10000000) (δ := 20423/1000000000) 813 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_442 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (442 : ℕ) / 2)) - ((17129/20000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log (442 : ℕ) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (442 : ℕ) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1356107/10000000) (δ := 20523/1000000000) 813 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_443 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (443 : ℕ) / 2)) - ((27371/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log (443 : ℕ) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (443 : ℕ) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3652731/10000000) (δ := 1019/50000000) 813 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_444 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (444 : ℕ) / 2)) - ((-722127/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log (444 : ℕ) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (444 : ℕ) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5944171/10000000) (δ := 20473/1000000000) 813 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_445 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (445 : ℕ) / 2)) - ((-247171/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log (445 : ℕ) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (445 : ℕ) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3738767/5000000) (δ := 20437/1000000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_446 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (446 : ℕ) / 2)) - ((-48621/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log (446 : ℕ) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (446 : ℕ) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2598179/5000000) (δ := 10183/500000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_447 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (447 : ℕ) / 2)) - ((195929/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log (447 : ℕ) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (447 : ℕ) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -730091/2500000) (δ := 20487/1000000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_448 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (448 : ℕ) / 2)) - ((966457/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log (448 : ℕ) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (448 : ℕ) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -649351/10000000) (δ := 5129/250000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_449 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (449 : ℕ) / 2)) - ((399071/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log (449 : ℕ) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (449 : ℕ) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10103/62500) (δ := 5129/250000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_450 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (450 : ℕ) / 2)) - ((9931/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log (450 : ℕ) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (450 : ℕ) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 969333/2500000) (δ := 20387/1000000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_451 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (451 : ℕ) / 2)) - ((-4827/6250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log (451 : ℕ) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (451 : ℕ) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1533301/2500000) (δ := 20487/1000000000) 813 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_452 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (452 : ℕ) / 2)) - ((-977611/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log (452 : ℕ) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (452 : ℕ) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7323969/10000000) (δ := 4079/200000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_453 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (453 : ℕ) / 2)) - ((-44433/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log (453 : ℕ) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (453 : ℕ) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5078057/10000000) (δ := 10229/500000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_454 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (454 : ℕ) / 2)) - ((52779/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log (454 : ℕ) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (454 : ℕ) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -113489/400000) (δ := 4099/200000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_455 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (455 : ℕ) / 2)) - ((971227/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log (455 : ℕ) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (455 : ℕ) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -601171/10000000) (δ := 5127/250000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_456 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (456 : ℕ) / 2)) - ((158979/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log (456 : ℕ) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (456 : ℕ) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 325981/2000000) (δ := 4089/200000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_457 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (457 : ℕ) / 2)) - ((28393/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log (457 : ℕ) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (457 : ℕ) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 241/625) (δ := 10229/500000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_458 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (458 : ℕ) / 2)) - ((-94741/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log (458 : ℕ) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (458 : ℕ) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 151933/250000) (δ := 4099/200000000) 813 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_459 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (459 : ℕ) / 2)) - ((-12307/12500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log (459 : ℕ) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (459 : ℕ) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7414101/10000000) (δ := 20401/1000000000) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_460 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (460 : ℕ) / 2)) - ((-30523/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log (460 : ℕ) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (460 : ℕ) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2601269/5000000) (δ := 20501/1000000000) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_461 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (461 : ℕ) / 2)) - ((363979/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log (461 : ℕ) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (461 : ℕ) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2995649/10000000) (δ := 159/7812500) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_462 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (462 : ℕ) / 2)) - ((950033/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log (462 : ℕ) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (462 : ℕ) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -793639/10000000) (δ := 20501/1000000000) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_463 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (463 : ℕ) / 2)) - ((846469/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log (463 : ℕ) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (463 : ℕ) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1403697/10000000) (δ := 20401/1000000000) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_464 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (464 : ℕ) / 2)) - ((32977/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log (464 : ℕ) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (464 : ℕ) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3596257/10000000) (δ := 10251/500000000) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_465 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (465 : ℕ) / 2)) - ((-676397/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log (465 : ℕ) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (465 : ℕ) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5784141/10000000) (δ := 20401/1000000000) 813 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_466 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (466 : ℕ) / 2)) - ((-499487/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log (466 : ℕ) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (466 : ℕ) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3870357/5000000) (δ := 10197/500000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_467 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (467 : ℕ) / 2)) - ((-304229/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log (467 : ℕ) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (467 : ℕ) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -139057/250000) (δ := 20459/1000000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_468 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (468 : ℕ) / 2)) - ((106863/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log (468 : ℕ) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (468 : ℕ) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1694261/5000000) (δ := 10247/500000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_469 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (469 : ℕ) / 2)) - ((883397/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log (469 : ℕ) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (469 : ℕ) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -152417/1250000) (δ := 2543/125000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_470 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (470 : ℕ) / 2)) - ((929379/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log (470 : ℕ) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (470 : ℕ) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37807/400000) (δ := 20359/1000000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_471 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (471 : ℕ) / 2)) - ((322861/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log (471 : ℕ) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (471 : ℕ) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3105113/10000000) (δ := 20459/1000000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_472 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (472 : ℕ) / 2)) - ((-508459/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log (472 : ℕ) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (472 : ℕ) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5260477/10000000) (δ := 5111/250000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_473 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (473 : ℕ) / 2)) - ((-984361/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log (473 : ℕ) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (473 : ℕ) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7411269/10000000) (δ := 20409/1000000000) 813 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_474 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (474 : ℕ) / 2)) - ((-155333/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log (474 : ℕ) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (474 : ℕ) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3075187/5000000) (δ := 5129/250000000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_475 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (475 : ℕ) / 2)) - ((-32649/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log (475 : ℕ) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (475 : ℕ) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1002157/2500000) (δ := 20487/1000000000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_476 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (476 : ℕ) / 2)) - ((146531/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log (476 : ℕ) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (476 : ℕ) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -935727/5000000) (δ := 20387/1000000000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_477 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (477 : ℕ) / 2)) - ((198909/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log (477 : ℕ) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (477 : ℕ) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2041/78125) (δ := 20487/1000000000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_478 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (478 : ℕ) / 2)) - ((576929/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log (478 : ℕ) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (478 : ℕ) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2389581/10000000) (δ := 319/15625000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_479 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (479 : ℕ) / 2)) - ((-46479/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log (479 : ℕ) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (479 : ℕ) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 225667/500000) (δ := 20337/1000000000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_480 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (480 : ℕ) / 2)) - ((-55191/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log (480 : ℕ) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (480 : ℕ) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6632831/10000000) (δ := 20337/1000000000) 813 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_481 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (481 : ℕ) / 2)) - ((-234193/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log (481 : ℕ) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (481 : ℕ) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3480107/5000000) (δ := 20473/1000000000) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_482 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (482 : ℕ) / 2)) - ((-360711/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log (482 : ℕ) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (482 : ℕ) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -969913/2000000) (δ := 2043/100000000) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_483 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (483 : ℕ) / 2)) - ((28497/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log (483 : ℕ) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (483 : ℕ) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2743387/10000000) (δ := 8/390625) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_484 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (484 : ℕ) / 2)) - ((967261/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log (484 : ℕ) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (484 : ℕ) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -641477/10000000) (δ := 2043/100000000) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_485 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (485 : ℕ) / 2)) - ((835153/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log (485 : ℕ) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (485 : ℕ) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 727981/5000000) (δ := 20473/1000000000) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_486 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (486 : ℕ) / 2)) - ((150529/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log (486 : ℕ) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (486 : ℕ) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3549233/10000000) (δ := 8/390625) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_487 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (487 : ℕ) / 2)) - ((-632253/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log (487 : ℕ) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (487 : ℕ) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1127627/2000000) (δ := 2043/100000000) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_488 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (488 : ℕ) / 2)) - ((-998623/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log (488 : ℕ) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (488 : ℕ) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7722769/10000000) (δ := 20373/1000000000) 813 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_489 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (489 : ℕ) / 2)) - ((-711181/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log (489 : ℕ) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (489 : ℕ) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5904931/10000000) (δ := 2559/125000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_490 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (490 : ℕ) / 2)) - ((39253/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log (490 : ℕ) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (490 : ℕ) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1914417/5000000) (δ := 10261/500000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_491 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (491 : ℕ) / 2)) - ((38153/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log (491 : ℕ) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (491 : ℕ) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1756903/10000000) (δ := 20331/1000000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_492 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (492 : ℕ) / 2)) - ((248071/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log (492 : ℕ) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (492 : ℕ) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 310759/10000000) (δ := 10211/500000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_493 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (493 : ℕ) / 2)) - ((581959/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log (493 : ℕ) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (493 : ℕ) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2374153/10000000) (δ := 10211/500000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_494 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (494 : ℕ) / 2)) - ((-201213/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log (494 : ℕ) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (494 : ℕ) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2216741/5000000) (δ := 10211/500000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_495 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (495 : ℕ) / 2)) - ((-854517/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log (495 : ℕ) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (495 : ℕ) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6488543/10000000) (δ := 20331/1000000000) 813 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_496 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (496 : ℕ) / 2)) - ((-240659/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log (496 : ℕ) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (496 : ℕ) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -286737/400000) (δ := 4103/200000000) 813 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_497 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (497 : ℕ) / 2)) - ((-57483/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log (497 : ℕ) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (497 : ℕ) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1024319/2000000) (δ := 2561/125000000) 813 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_498 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (498 : ℕ) / 2)) - ((66551/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log (498 : ℕ) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (498 : ℕ) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3078933/10000000) (δ := 4073/200000000) 813 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_499 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (499 : ℕ) / 2)) - ((914659/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log (499 : ℕ) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (499 : ℕ) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -208067/2000000) (δ := 2561/125000000) 813 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos813o2_br_500 :
    |Real.cos (((813 : ℕ) : ℝ) * (Real.log (500 : ℕ) / 2)) - ((460981/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log (500 : ℕ) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (500 : ℕ) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 994197/10000000) (δ := 4073/200000000) 813 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos813o2_br_500
end AxiomAudit
