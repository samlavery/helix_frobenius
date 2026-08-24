import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table
import RequestProject.DVPLog500Table
import RequestProject.DVPLog1000Table

/-!
# The cosine table at `t = 1142/2` (rung-571; halved brackets, N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos1142o2_br_2 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (2 : ℕ) / 2)) - ((9985611/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (2 : ℕ) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1341293/100000000) (δ := 142839/5000000000) 1142 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_3 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (3 : ℕ) / 2)) - ((5310679/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (3 : ℕ) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25273399/100000000) (δ := 285581/10000000000) 1142 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_4 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (4 : ℕ) / 2)) - ((2485629/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (4 : ℕ) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2681871/100000000) (δ := 17853/625000000) 1142 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_5 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (5 : ℕ) / 2)) - ((-731529/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (5 : ℕ) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8220073/20000000) (δ := 285519/10000000000) 1142 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_6 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (6 : ℕ) / 2)) - ((2424449/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (6 : ℕ) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13306989/50000000) (δ := 4461/156250000) 1142 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_7 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (7 : ℕ) / 2)) - ((1065239/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (7 : ℕ) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25227593/100000000) (δ := 285509/10000000000) 1142 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_8 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (8 : ℕ) / 2)) - ((4935419/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (8 : ℕ) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -80449/2000000) (δ := 285571/10000000000) 1142 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_9 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (9 : ℕ) / 2)) - ((-4359081/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (9 : ℕ) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10109217/20000000) (δ := 142821/5000000000) 1142 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_10 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (10 : ℕ) / 2)) - ((-24421/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (10 : ℕ) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39758359/100000000) (δ := 285607/10000000000) 1142 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_11 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (11 : ℕ) / 2)) - ((1719303/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (11 : ℕ) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1340523/10000000) (δ := 285653/10000000000) 1142 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_12 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (12 : ℕ) / 2)) - ((4373179/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (12 : ℕ) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27954557/100000000) (δ := 35697/1250000000) 1142 226
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_13 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (13 : ℕ) / 2)) - ((8231259/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (13 : ℕ) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15097557/100000000) (δ := 28553/1000000000) 1142 233
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_14 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (14 : ℕ) / 2)) - ((972983/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (14 : ℕ) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6642043/25000000) (δ := 28557/1000000000) 1142 240
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_15 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (15 : ℕ) / 2)) - ((806193/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (15 : ℕ) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 98923/625000) (δ := 285663/10000000000) 1142 246
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_16 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (16 : ℕ) / 2)) - ((305337/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (16 : ℕ) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5363029/100000000) (δ := 285509/10000000000) 1142 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_17 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (17 : ℕ) / 2)) - ((-9879507/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (17 : ℕ) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 74654973/100000000) (δ := 285653/10000000000) 1142 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_18 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (18 : ℕ) / 2)) - ((-1208797/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (18 : ℕ) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51886663/100000000) (δ := 71421/2500000000) 1142 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_19 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (19 : ℕ) / 2)) - ((-8665389/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (19 : ℕ) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65475547/100000000) (δ := 7139/250000000) 1142 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_20 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (20 : ℕ) / 2)) - ((68157/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (20 : ℕ) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1920889/5000000) (δ := 28553/1000000000) 1142 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_21 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (21 : ℕ) / 2)) - ((-542823/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (21 : ℕ) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25250139/50000000) (δ := 285689/10000000000) 1142 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_22 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (22 : ℕ) / 2)) - ((8310339/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (22 : ℕ) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14745809/100000000) (δ := 35697/1250000000) 1142 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_23 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (23 : ℕ) / 2)) - ((4712779/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (23 : ℕ) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1702979/20000000) (δ := 14277/500000000) 1142 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_24 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (24 : ℕ) / 2)) - ((3884887/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (24 : ℕ) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -915473/3125000) (δ := 71413/2500000000) 1142 289
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_25 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (25 : ℕ) / 2)) - ((-1978603/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (25 : ℕ) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -584997/781250) (δ := 142819/5000000000) 1142 293
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_26 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (26 : ℕ) / 2)) - ((4261893/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (26 : ℕ) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6878489/50000000) (δ := 5711/200000000) 1142 296
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_27 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (27 : ℕ) / 2)) - ((-4970413/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log (27 : ℕ) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (27 : ℕ) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7581877/10000000) (δ := 14277/500000000) 1142 300
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_28 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (28 : ℕ) / 2)) - ((4389649/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (28 : ℕ) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27908751/100000000) (δ := 285647/10000000000) 1142 303
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_29 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (29 : ℕ) / 2)) - ((1994929/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (29 : ℕ) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1780659/100000000) (δ := 285571/10000000000) 1142 306
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_30 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (30 : ℕ) / 2)) - ((4183883/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (30 : ℕ) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14485673/100000000) (δ := 285617/10000000000) 1142 309
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_31 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (31 : ℕ) / 2)) - ((4495901/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log (31 : ℕ) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (31 : ℕ) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5661299/50000000) (δ := 142801/5000000000) 1142 312
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_32 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (32 : ℕ) / 2)) - ((4821321/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (32 : ℕ) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -837951/12500000) (δ := 142793/5000000000) 1142 315
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_33 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (33 : ℕ) / 2)) - ((9471/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (33 : ℕ) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9669479/25000000) (δ := 28557/1000000000) 1142 318
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_34 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (34 : ℕ) / 2)) - ((-4891177/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (34 : ℕ) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36657197/50000000) (δ := 35697/1250000000) 1142 320
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_35 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (35 : ℕ) / 2)) - ((1610283/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (35 : ℕ) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7936029/50000000) (δ := 285611/10000000000) 1142 323
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_36 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (36 : ℕ) / 2)) - ((-1059479/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (36 : ℕ) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26613621/50000000) (δ := 285607/10000000000) 1142 326
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_37 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (37 : ℕ) / 2)) - ((1164393/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (37 : ℕ) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23734217/100000000) (δ := 71413/2500000000) 1142 328
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_38 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (38 : ℕ) / 2)) - ((-2230111/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (38 : ℕ) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33408063/50000000) (δ := 285637/10000000000) 1142 331
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_39 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (39 : ℕ) / 2)) - ((1836621/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log (39 : ℕ) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (39 : ℕ) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10175129/100000000) (δ := 285693/10000000000) 1142 333
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_40 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (40 : ℕ) / 2)) - ((875959/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (40 : ℕ) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37077201/100000000) (δ := 5711/200000000) 1142 335
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_41 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (41 : ℕ) / 2)) - ((-2480369/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (41 : ℕ) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75404801/100000000) (δ := 285597/10000000000) 1142 337
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_42 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (42 : ℕ) / 2)) - ((-4819141/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (42 : ℕ) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51840857/100000000) (δ := 71403/2500000000) 1142 340
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_43 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (43 : ℕ) / 2)) - ((3585433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (43 : ℕ) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6020447/20000000) (δ := 71389/2500000000) 1142 342
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_44 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (44 : ℕ) / 2)) - ((4000137/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (44 : ℕ) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4021597/25000000) (δ := 4461/156250000) 1142 344
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_45 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (45 : ℕ) / 2)) - ((9294573/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log (45 : ℕ) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (45 : ℕ) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9446433/100000000) (δ := 285643/10000000000) 1142 346
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_46 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (46 : ℕ) / 2)) - ((9232749/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (46 : ℕ) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9856901/100000000) (δ := 142793/5000000000) 1142 348
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_47 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (47 : ℕ) / 2)) - ((485767/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (47 : ℕ) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8506867/50000000) (δ := 28553/1000000000) 1142 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_48 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (48 : ℕ) / 2)) - ((846357/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (48 : ℕ) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15317857/50000000) (δ := 142837/5000000000) 1142 352
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_49 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (49 : ℕ) / 2)) - ((-4326587/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (49 : ℕ) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -504559/1000000) (δ := 142793/5000000000) 1142 354
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_50 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (50 : ℕ) / 2)) - ((-4978493/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (50 : ℕ) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15244039/20000000) (δ := 285561/10000000000) 1142 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_51 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (51 : ℕ) / 2)) - ((-3935547/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (51 : ℕ) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 49382287/100000000) (δ := 28557/1000000000) 1142 357
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_52 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (52 : ℕ) / 2)) - ((8791809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (52 : ℕ) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12416399/100000000) (δ := 285627/10000000000) 1142 359
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_53 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (53 : ℕ) / 2)) - ((1843471/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (53 : ℕ) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29829811/100000000) (δ := 3569/125000000) 1142 361
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_54 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (54 : ℕ) / 2)) - ((-4992379/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (54 : ℕ) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77159349/100000000) (δ := 14277/500000000) 1142 363
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_55 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (55 : ℕ) / 2)) - ((4466517/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (55 : ℕ) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27694421/100000000) (δ := 57107/2000000000) 1142 364
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_56 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (56 : ℕ) / 2)) - ((1950619/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (56 : ℕ) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29250757/100000000) (δ := 71381/2500000000) 1142 366
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_57 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (57 : ℕ) / 2)) - ((-1766229/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (57 : ℕ) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 331657/500000) (δ := 71413/2500000000) 1142 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_58 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (58 : ℕ) / 2)) - ((9998451/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (58 : ℕ) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5501/1250000) (δ := 285509/10000000000) 1142 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_59 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (59 : ℕ) / 2)) - ((-117261/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (59 : ℕ) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -557573/800000) (δ := 142819/5000000000) 1142 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_60 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (60 : ℕ) / 2)) - ((1081151/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (60 : ℕ) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6572547/50000000) (δ := 285693/10000000000) 1142 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_61 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (61 : ℕ) / 2)) - ((-8580909/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (61 : ℕ) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65058413/100000000) (δ := 285653/10000000000) 1142 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_62 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (62 : ℕ) / 2)) - ((921363/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (62 : ℕ) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9980591/100000000) (δ := 142839/5000000000) 1142 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_63 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (63 : ℕ) / 2)) - ((-9938819/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (63 : ℕ) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18943241/25000000) (δ := 142767/5000000000) 1142 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_64 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (64 : ℕ) / 2)) - ((9486599/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (64 : ℕ) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4022807/50000000) (δ := 14277/500000000) 1142 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_65 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (65 : ℕ) / 2)) - ((-1566323/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (65 : ℕ) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7024651/12500000) (δ := 285591/10000000000) 1142 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_66 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (66 : ℕ) / 2)) - ((-29939/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (66 : ℕ) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8003699/20000000) (δ := 285647/10000000000) 1142 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_67 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (67 : ℕ) / 2)) - ((3815449/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (67 : ℕ) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3513579/20000000) (δ := 11423/400000000) 1142 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_68 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (68 : ℕ) / 2)) - ((-9657079/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (68 : ℕ) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14394763/20000000) (δ := 4461/156250000) 1142 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_69 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (69 : ℕ) / 2)) - ((2175397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (69 : ℕ) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1689379/5000000) (δ := 285643/10000000000) 1142 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_70 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (70 : ℕ) / 2)) - ((8357719/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (70 : ℕ) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14531479/100000000) (δ := 35711/1250000000) 1142 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_71 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (71 : ℕ) / 2)) - ((-1471379/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (71 : ℕ) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14984253/25000000) (δ := 142793/5000000000) 1142 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_72 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (72 : ℕ) / 2)) - ((-5744373/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (72 : ℕ) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54567821/100000000) (δ := 28553/1000000000) 1142 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_73 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (73 : ℕ) / 2)) - ((830983/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (73 : ℕ) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -230439/1562500) (δ := 142801/5000000000) 1142 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_74 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (74 : ℕ) / 2)) - ((1249963/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (74 : ℕ) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22392211/100000000) (δ := 285529/10000000000) 1142 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_75 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (75 : ℕ) / 2)) - ((-649021/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (75 : ℕ) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 56927331/100000000) (δ := 57109/2000000000) 1142 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_76 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (76 : ℕ) / 2)) - ((-4574927/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (76 : ℕ) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2129897/3125000) (δ := 285689/10000000000) 1142 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_77 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (77 : ℕ) / 2)) - ((63773/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (77 : ℕ) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3863211/10000000) (δ := 142821/5000000000) 1142 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_78 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (78 : ℕ) / 2)) - ((4478867/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (78 : ℕ) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11515707/100000000) (δ := 285633/10000000000) 1142 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_79 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (79 : ℕ) / 2)) - ((1725457/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (79 : ℕ) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2650777/20000000) (δ := 4461/156250000) 1142 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_80 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (80 : ℕ) / 2)) - ((704307/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (80 : ℕ) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17868311/50000000) (δ := 285627/10000000000) 1142 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_81 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (81 : ℕ) / 2)) - ((-3099953/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (81 : ℕ) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 55988177/100000000) (δ := 57111/2000000000) 1142 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_82 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (82 : ℕ) / 2)) - ((-492009/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (82 : ℕ) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37032111/50000000) (δ := 3569/125000000) 1142 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_83 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (83 : ℕ) / 2)) - ((-8964471/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (83 : ℕ) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33531029/50000000) (δ := 285663/10000000000) 1142 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_84 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (84 : ℕ) / 2)) - ((-660261/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (84 : ℕ) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1063643/2000000) (δ := 142767/2500000000) 1142 403
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_85 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (85 : ℕ) / 2)) - ((-164223/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (85 : ℕ) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41325009/100000000) (δ := 71399/2500000000) 1142 404
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_86 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (86 : ℕ) / 2)) - ((3079397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (86 : ℕ) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31444241/100000000) (δ := 285679/10000000000) 1142 405
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_87 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (87 : ℕ) / 2)) - ((1180091/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (87 : ℕ) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23492027/100000000) (δ := 71413/2500000000) 1142 406
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_88 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (88 : ℕ) / 2)) - ((7667209/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (88 : ℕ) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17426967/100000000) (δ := 285581/10000000000) 1142 407
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_89 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (89 : ℕ) / 2)) - ((8636907/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (89 : ℕ) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13206237/100000000) (δ := 285509/10000000000) 1142 408
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_90 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (90 : ℕ) / 2)) - ((2270869/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (90 : ℕ) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2696753/25000000) (δ := 142783/5000000000) 1142 409
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_91 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (91 : ℕ) / 2)) - ((919023/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (91 : ℕ) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2532509/25000000) (δ := 285519/5000000000) 1142 410
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_92 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (92 : ℕ) / 2)) - ((9013589/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (92 : ℕ) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -279937/2500000) (δ := 28551/1000000000) 1142 411
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_93 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (93 : ℕ) / 2)) - ((8482837/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (93 : ℕ) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2790303/20000000) (δ := 285581/10000000000) 1142 412
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_94 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (94 : ℕ) / 2)) - ((463967/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (94 : ℕ) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -917787/5000000) (δ := 285653/10000000000) 1142 413
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_95 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (95 : ℕ) / 2)) - ((701423/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (95 : ℕ) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3046987/12500000) (δ := 142839/5000000000) 1142 414
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_96 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (96 : ℕ) / 2)) - ((359461/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (96 : ℕ) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31977721/100000000) (δ := 142803/5000000000) 1142 415
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_97 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (97 : ℕ) / 2)) - ((-148541/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (97 : ℕ) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41128383/100000000) (δ := 285669/10000000000) 1142 416
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_98 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (98 : ℕ) / 2)) - ((-240179/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (98 : ℕ) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51796479/100000000) (δ := 285663/10000000000) 1142 417
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_99 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (99 : ℕ) / 2)) - ((-1043127/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (99 : ℕ) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -63950601/100000000) (δ := 71403/2500000000) 1142 418
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_100 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (100 : ℕ) / 2)) - ((-1998471/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (100 : ℕ) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77562201/100000000) (δ := 71421/2500000000) 1142 419
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_101 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (101 : ℕ) / 2)) - ((-4229883/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (101 : ℕ) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64479759/100000000) (δ := 71421/2500000000) 1142 419
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_102 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (102 : ℕ) / 2)) - ((-214823/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (102 : ℕ) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12010427/25000000) (δ := 285647/10000000000) 1142 420
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_103 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (103 : ℕ) / 2)) - ((3537527/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (103 : ℕ) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30230403/100000000) (δ := 11423/400000000) 1142 421
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_104 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (104 : ℕ) / 2)) - ((4517401/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (104 : ℕ) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11074393/100000000) (δ := 4461/156250000) 1142 422
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_105 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (105 : ℕ) / 2)) - ((9301317/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (105 : ℕ) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9400627/100000000) (δ := 285571/10000000000) 1142 423
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_106 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (106 : ℕ) / 2)) - ((1591443/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (106 : ℕ) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31171817/100000000) (δ := 285643/10000000000) 1142 424
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_107 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (107 : ℕ) / 2)) - ((-562731/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log (107 : ℕ) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (107 : ℕ) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10842411/20000000) (δ := 57103/2000000000) 1142 425
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_108 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (108 : ℕ) / 2)) - ((-9999987/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log (108 : ℕ) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (108 : ℕ) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9812491/12500000) (δ := 17851/625000000) 1142 426
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_109 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (109 : ℕ) / 2)) - ((-2621467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (109 : ℕ) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53067037/100000000) (δ := 17851/625000000) 1142 426
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_110 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (110 : ℕ) / 2)) - ((2469819/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (110 : ℕ) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13176921/50000000) (δ := 57109/2000000000) 1142 427
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_111 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (111 : ℕ) / 2)) - ((9981071/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (111 : ℕ) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -384617/25000000) (δ := 28553/1000000000) 1142 428
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_112 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (112 : ℕ) / 2)) - ((27217/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (112 : ℕ) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3823917/12500000) (δ := 285601/10000000000) 1142 429
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_113 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (113 : ℕ) / 2)) - ((-7581187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (113 : ℕ) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60780493/100000000) (δ := 142837/5000000000) 1142 430
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_114 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (114 : ℕ) / 2)) - ((-4283497/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log (114 : ℕ) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (114 : ℕ) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32495411/50000000) (δ := 142837/5000000000) 1142 430
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_115 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (115 : ℕ) / 2)) - ((1321153/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (115 : ℕ) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8146189/25000000) (δ := 285657/10000000000) 1142 431
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_116 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (116 : ℕ) / 2)) - ((9993493/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (116 : ℕ) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -450963/50000000) (δ := 285617/10000000000) 1142 432
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_117 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (117 : ℕ) / 2)) - ((1522889/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (117 : ℕ) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17723907/50000000) (δ := 142757/5000000000) 1142 433
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_118 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (118 : ℕ) / 2)) - ((-298533/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (118 : ℕ) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17759301/25000000) (δ := 285561/10000000000) 1142 434
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_119 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (119 : ℕ) / 2)) - ((-197593/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (119 : ℕ) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24713333/50000000) (δ := 285561/10000000000) 1142 434
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_120 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (120 : ℕ) / 2)) - ((4452893/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (120 : ℕ) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2951129/25000000) (δ := 285633/10000000000) 1142 435
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_121 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (121 : ℕ) / 2)) - ((956053/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (121 : ℕ) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26809747/100000000) (δ := 4461/156250000) 1142 436
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_122 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (122 : ℕ) / 2)) - ((-8843797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (122 : ℕ) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4149937/6250000) (δ := 35697/1250000000) 1142 437
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_123 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (123 : ℕ) / 2)) - ((-4209463/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (123 : ℕ) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10026423/20000000) (δ := 285627/10000000000) 1142 437
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_124 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (124 : ℕ) / 2)) - ((4704361/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (124 : ℕ) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8640013/100000000) (δ := 17853/625000000) 1142 438
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_125 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (125 : ℕ) / 2)) - ((217837/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (125 : ℕ) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6755993/20000000) (δ := 3569/125000000) 1142 439
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_126 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (126 : ℕ) / 2)) - ((-998373/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (126 : ℕ) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77113543/100000000) (δ := 285611/10000000000) 1142 440
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_127 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (127 : ℕ) / 2)) - ((1410539/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (127 : ℕ) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 446647/1250000) (δ := 35699/1250000000) 1142 440
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_128 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (128 : ℕ) / 2)) - ((1860687/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (128 : ℕ) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9386193/100000000) (δ := 14277/500000000) 1142 441
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_129 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (129 : ℕ) / 2)) - ((-3002797/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (129 : ℕ) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55374921/100000000) (δ := 71417/2500000000) 1142 442
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_130 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (130 : ℕ) / 2)) - ((-5838549/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (130 : ℕ) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54856629/100000000) (δ := 71417/2500000000) 1142 442
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_131 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (131 : ℕ) / 2)) - ((4796059/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (131 : ℕ) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3582447/50000000) (δ := 71399/2500000000) 1142 443
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_132 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (132 : ℕ) / 2)) - ((-417347/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (132 : ℕ) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41359073/100000000) (δ := 285679/10000000000) 1142 444
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_133 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (133 : ℕ) / 2)) - ((-4419863/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (133 : ℕ) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66377207/100000000) (δ := 285679/10000000000) 1142 444
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_134 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (134 : ℕ) / 2)) - ((3983249/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (134 : ℕ) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16226603/100000000) (δ := 571151/10000000000) 1142 445
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_135 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (135 : ℕ) / 2)) - ((1810279/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (135 : ℕ) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34719119/100000000) (δ := 285581/10000000000) 1142 446
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_136 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (136 : ℕ) / 2)) - ((-1900773/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (136 : ℕ) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70631809/100000000) (δ := 142811/5000000000) 1142 446
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_137 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (137 : ℕ) / 2)) - ((748307/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (137 : ℕ) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9066127/50000000) (δ := 142847/5000000000) 1142 447
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_138 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (138 : ℕ) / 2)) - ((206071/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (138 : ℕ) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35129587/100000000) (δ := 285637/10000000000) 1142 448
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_139 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (139 : ℕ) / 2)) - ((-1139321/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (139 : ℕ) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16985049/25000000) (δ := 142783/5000000000) 1142 448
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_140 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (140 : ℕ) / 2)) - ((8639997/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (140 : ℕ) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13190901/100000000) (δ := 142819/5000000000) 1142 449
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_141 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (141 : ℕ) / 2)) - ((-602123/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (141 : ℕ) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -42287847/100000000) (δ := 28551/1000000000) 1142 450
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_142 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (142 : ℕ) / 2)) - ((-1396659/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (142 : ℕ) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58596433/100000000) (δ := 28551/1000000000) 1142 450
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_143 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (143 : ℕ) / 2)) - ((4988539/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (143 : ℕ) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21163/1250000) (δ := 142811/5000000000) 1142 451
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_144 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (144 : ℕ) / 2)) - ((-3087643/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (144 : ℕ) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55909827/100000000) (δ := 285653/10000000000) 1142 452
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_145 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (145 : ℕ) / 2)) - ((-719573/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (145 : ℕ) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4288031/10000000) (δ := 5711/200000000) 1142 452
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_146 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (146 : ℕ) / 2)) - ((319989/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (146 : ℕ) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -643547/4000000) (δ := 11421/400000000) 1142 453
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_147 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (147 : ℕ) / 2)) - ((-4968421/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (147 : ℕ) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15145717/20000000) (δ := 285597/10000000000) 1142 454
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_148 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (148 : ℕ) / 2)) - ((1331847/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (148 : ℕ) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1315727/6250000) (δ := 142803/5000000000) 1142 454
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_149 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (149 : ℕ) / 2)) - ((-251499/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (149 : ℕ) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39898723/100000000) (δ := 142767/5000000000) 1142 455
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_150 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (150 : ℕ) / 2)) - ((-3036337/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (150 : ℕ) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2223413/4000000) (δ := 285669/10000000000) 1142 455
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_151 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (151 : ℕ) / 2)) - ((4824537/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (151 : ℕ) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6642643/100000000) (δ := 14277/500000000) 1142 456
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_152 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (152 : ℕ) / 2)) - ((-9352961/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (152 : ℕ) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69497283/100000000) (δ := 71403/2500000000) 1142 457
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_153 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (153 : ℕ) / 2)) - ((5699231/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (153 : ℕ) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12054801/50000000) (δ := 71403/2500000000) 1142 457
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_154 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (154 : ℕ) / 2)) - ((-11243/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (154 : ℕ) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2498293/6250000) (δ := 71421/2500000000) 1142 458
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_155 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (155 : ℕ) / 2)) - ((-5021591/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (155 : ℕ) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52422249/100000000) (δ := 285519/10000000000) 1142 458
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_156 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (156 : ℕ) / 2)) - ((2176653/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (156 : ℕ) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6428143/50000000) (δ := 71389/2500000000) 1142 459
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_157 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (157 : ℕ) / 2)) - ((-1249967/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (157 : ℕ) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 78358109/100000000) (δ := 71389/2500000000) 1142 459
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_158 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (158 : ℕ) / 2)) - ((8885909/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (158 : ℕ) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5956653/50000000) (δ := 11423/400000000) 1142 460
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_159 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (159 : ℕ) / 2)) - ((-5918109/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (159 : ℕ) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1721953/3125000) (δ := 285699/10000000000) 1142 461
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_160 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (160 : ℕ) / 2)) - ((96861/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (160 : ℕ) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8599011/25000000) (δ := 285699/10000000000) 1142 461
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_161 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (161 : ℕ) / 2)) - ((27409/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (161 : ℕ) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16871601/50000000) (δ := 4463/156250000) 1142 462
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_162 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (162 : ℕ) / 2)) - ((-180327/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (162 : ℕ) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27323799/50000000) (δ := 4463/156250000) 1142 462
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_163 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (163 : ℕ) / 2)) - ((8345921/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (163 : ℕ) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1823139/12500000) (δ := 7139/250000000) 1142 463
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_164 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (164 : ℕ) / 2)) - ((-1946119/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (164 : ℕ) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 72723643/100000000) (δ := 7139/250000000) 1142 463
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_165 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (165 : ℕ) / 2)) - ((4976559/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (165 : ℕ) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 484347/20000000) (δ := 35711/1250000000) 1142 464
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_166 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (166 : ℕ) / 2)) - ((-9189329/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (166 : ℕ) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13680813/20000000) (δ := 17851/625000000) 1142 465
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_167 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (167 : ℕ) / 2)) - ((7691281/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (167 : ℕ) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17333013/100000000) (δ := 285587/10000000000) 1142 465
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_168 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (168 : ℕ) / 2)) - ((-5729833/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (168 : ℕ) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27261721/50000000) (δ := 142829/5000000000) 1142 466
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_169 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (169 : ℕ) / 2)) - ((3550459/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (169 : ℕ) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7548957/25000000) (δ := 142829/5000000000) 1142 466
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_170 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (170 : ℕ) / 2)) - ((-1354099/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log (170 : ℕ) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (170 : ℕ) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10666397/25000000) (δ := 285673/10000000000) 1142 467
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_171 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (171 : ℕ) / 2)) - ((-22341/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (171 : ℕ) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8211743/20000000) (δ := 28553/1000000000) 1142 467
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_172 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (172 : ℕ) / 2)) - ((2565041/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (172 : ℕ) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1639241/5000000) (δ := 142801/5000000000) 1142 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_173 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (173 : ℕ) / 2)) - ((-4150111/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (173 : ℕ) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24984391/50000000) (δ := 285601/10000000000) 1142 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_174 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (174 : ℕ) / 2)) - ((2729383/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (174 : ℕ) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24834033/100000000) (δ := 285529/10000000000) 1142 469
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_175 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (175 : ℕ) / 2)) - ((-1300741/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (175 : ℕ) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5697171/10000000) (δ := 142837/5000000000) 1142 469
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_176 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (176 : ℕ) / 2)) - ((7311713/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (176 : ℕ) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18768973/100000000) (δ := 142773/5000000000) 1142 470
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_177 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (177 : ℕ) / 2)) - ((-3958591/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (177 : ℕ) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31055161/50000000) (δ := 142773/5000000000) 1142 470
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_178 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (178 : ℕ) / 2)) - ((8354349/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (178 : ℕ) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -113647/781250) (δ := 142793/5000000000) 1142 471
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_179 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (179 : ℕ) / 2)) - ((-2163871/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (179 : ℕ) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65426017/100000000) (δ := 285617/10000000000) 1142 471
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_180 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (180 : ℕ) / 2)) - ((4423133/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log (180 : ℕ) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (180 : ℕ) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12127591/100000000) (δ := 142757/5000000000) 1142 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_181 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (181 : ℕ) / 2)) - ((-1789217/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (181 : ℕ) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16739691/25000000) (δ := 142757/5000000000) 1142 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_182 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (182 : ℕ) / 2)) - ((896561/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (182 : ℕ) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11471329/100000000) (δ := 142821/5000000000) 1142 473
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_183 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (183 : ℕ) / 2)) - ((-278381/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (183 : ℕ) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33374267/50000000) (δ := 285561/10000000000) 1142 473
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_184 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (184 : ℕ) / 2)) - ((8768517/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (184 : ℕ) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12538059/100000000) (δ := 28557/1000000000) 1142 474
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_185 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (185 : ℕ) / 2)) - ((-4267221/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (185 : ℕ) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64833869/100000000) (δ := 285633/10000000000) 1142 474
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_186 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (186 : ℕ) / 2)) - ((8186823/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (186 : ℕ) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7646047/50000000) (δ := 57101/2000000000) 1142 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_187 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (187 : ℕ) / 2)) - ((-7702429/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (187 : ℕ) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7656307/12500000) (δ := 57101/2000000000) 1142 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_188 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (188 : ℕ) / 2)) - ((705369/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (188 : ℕ) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19696319/100000000) (δ := 35697/1250000000) 1142 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_189 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (189 : ℕ) / 2)) - ((-48549/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (189 : ℕ) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 56033983/100000000) (δ := 285627/10000000000) 1142 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_190 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (190 : ℕ) / 2)) - ((5159681/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log (190 : ℕ) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (190 : ℕ) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12858237/50000000) (δ := 17853/625000000) 1142 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_191 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (191 : ℕ) / 2)) - ((-3875313/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (191 : ℕ) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 49218711/100000000) (δ := 17853/625000000) 1142 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_192 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (192 : ℕ) / 2)) - ((117911/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (192 : ℕ) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -333183/1000000) (δ := 285683/10000000000) 1142 478
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_193 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (193 : ℕ) / 2)) - ((-313307/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (193 : ℕ) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4083747/10000000) (δ := 285683/10000000000) 1142 478
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_194 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (194 : ℕ) / 2)) - ((-319033/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (194 : ℕ) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21234481/50000000) (δ := 35699/1250000000) 1142 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_195 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (195 : ℕ) / 2)) - ((1638251/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (195 : ℕ) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30924523/100000000) (δ := 35699/1250000000) 1142 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_196 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (196 : ℕ) / 2)) - ((-1316691/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (196 : ℕ) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53137057/100000000) (δ := 8927/312500000) 1142 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_197 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (197 : ℕ) / 2)) - ((1421273/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (197 : ℕ) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3901969/20000000) (δ := 285539/10000000000) 1142 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_198 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (198 : ℕ) / 2)) - ((-4314173/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (198 : ℕ) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3264559/5000000) (δ := 57107/2000000000) 1142 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_199 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (199 : ℕ) / 2)) - ((9651091/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (199 : ℕ) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1324683/20000000) (δ := 57107/2000000000) 1142 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_200 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (200 : ℕ) / 2)) - ((-4999473/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (200 : ℕ) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19544213/25000000) (δ := 71417/2500000000) 1142 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_201 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (201 : ℕ) / 2)) - ((9528837/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (201 : ℕ) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -770479/10000000) (δ := 285607/10000000000) 1142 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_202 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (202 : ℕ) / 2)) - ((-2040371/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (202 : ℕ) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7892219/12500000) (δ := 71399/2500000000) 1142 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_203 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (203 : ℕ) / 2)) - ((2957389/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (203 : ℕ) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -732739/3125000) (δ := 71381/2500000000) 1142 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_204 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (204 : ℕ) / 2)) - ((-1464181/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (204 : ℕ) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23349851/50000000) (δ := 71381/2500000000) 1142 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_205 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (205 : ℕ) / 2)) - ((-32617/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (205 : ℕ) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40575181/100000000) (δ := 71413/2500000000) 1142 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_206 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (206 : ℕ) / 2)) - ((25211/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (206 : ℕ) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 902807/3125000) (δ := 71413/2500000000) 1142 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_207 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (207 : ℕ) / 2)) - ((-7115287/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (207 : ℕ) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59061693/100000000) (δ := 142811/5000000000) 1142 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_208 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (208 : ℕ) / 2)) - ((185031/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (208 : ℕ) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4866907/50000000) (δ := 285581/10000000000) 1142 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_209 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (209 : ℕ) / 2)) - ((-4999537/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (209 : ℕ) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 78199569/100000000) (δ := 285581/10000000000) 1142 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_210 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (210 : ℕ) / 2)) - ((9091123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (210 : ℕ) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5370603/50000000) (δ := 285509/10000000000) 1142 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_211 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (211 : ℕ) / 2)) - ((-6534613/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (211 : ℕ) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 57073609/100000000) (δ := 285509/10000000000) 1142 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_212 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (212 : ℕ) / 2)) - ((267021/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (212 : ℕ) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8128099/25000000) (δ := 142783/5000000000) 1142 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_213 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (213 : ℕ) / 2)) - ((183183/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (213 : ℕ) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17332163/50000000) (δ := 285637/10000000000) 1142 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_214 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (214 : ℕ) / 2)) - ((-151557/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (214 : ℕ) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27776317/50000000) (δ := 57113/2000000000) 1142 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_215 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (215 : ℕ) / 2)) - ((9047957/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (215 : ℕ) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1374677/12500000) (δ := 57113/2000000000) 1142 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_216 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (216 : ℕ) / 2)) - ((-9986469/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (216 : ℕ) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38619563/50000000) (δ := 57113/2000000000) 1142 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_217 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (217 : ℕ) / 2)) - ((339701/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (217 : ℕ) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13905709/100000000) (δ := 28551/1000000000) 1142 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_218 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (218 : ℕ) / 2)) - ((-1194749/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (218 : ℕ) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25863229/50000000) (δ := 285693/10000000000) 1142 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_219 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (219 : ℕ) / 2)) - ((-18769/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (219 : ℕ) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20010391/50000000) (δ := 142811/5000000000) 1142 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_220 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (220 : ℕ) / 2)) - ((2699279/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (220 : ℕ) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25013263/100000000) (δ := 142811/5000000000) 1142 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_221 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (221 : ℕ) / 2)) - ((-360433/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (221 : ℕ) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67326389/100000000) (δ := 285653/10000000000) 1142 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_222 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (222 : ℕ) / 2)) - ((77607/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (222 : ℕ) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1440237/50000000) (δ := 285653/10000000000) 1142 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_223 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (223 : ℕ) / 2)) - ((-3854609/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (223 : ℕ) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30638543/50000000) (δ := 285653/10000000000) 1142 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_224 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (224 : ℕ) / 2)) - ((180827/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (224 : ℕ) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6386383/20000000) (δ := 142839/5000000000) 1142 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_225 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (225 : ℕ) / 2)) - ((2999217/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (225 : ℕ) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6330929/20000000) (δ := 142839/5000000000) 1142 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_226 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (226 : ℕ) / 2)) - ((-7919983/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (226 : ℕ) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31060893/50000000) (δ := 285503/5000000000) 1142 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_227 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (227 : ℕ) / 2)) - ((9993477/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (227 : ℕ) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 903053/100000000) (δ := 285597/10000000000) 1142 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_228 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (228 : ℕ) / 2)) - ((-1034777/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (228 : ℕ) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 63650243/100000000) (δ := 285597/10000000000) 1142 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_229 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (229 : ℕ) / 2)) - ((1632249/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (229 : ℕ) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -773907/2500000) (δ := 142767/5000000000) 1142 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_230 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (230 : ℕ) / 2)) - ((1577717/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (230 : ℕ) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15622089/50000000) (δ := 285669/10000000000) 1142 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_231 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (231 : ℕ) / 2)) - ((-8334907/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (231 : ℕ) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12780959/20000000) (δ := 14277/500000000) 1142 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_232 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (232 : ℕ) / 2)) - ((2489949/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (232 : ℕ) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -448501/20000000) (δ := 14277/500000000) 1142 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_233 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (233 : ℕ) / 2)) - ((-7141657/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (233 : ℕ) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59155697/100000000) (δ := 285663/10000000000) 1142 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_234 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (234 : ℕ) / 2)) - ((990977/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (234 : ℕ) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36788393/100000000) (δ := 285591/10000000000) 1142 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_235 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (235 : ℕ) / 2)) - ((5707013/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (235 : ℕ) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24085917/100000000) (δ := 285591/10000000000) 1142 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_236 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (236 : ℕ) / 2)) - ((-969777/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (236 : ℕ) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -72377783/100000000) (δ := 285519/10000000000) 1142 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_237 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (237 : ℕ) / 2)) - ((4433237/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (237 : ℕ) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30047/250000) (δ := 71421/2500000000) 1142 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_238 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (238 : ℕ) / 2)) - ((-3453833/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (238 : ℕ) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48086087/100000000) (δ := 285519/10000000000) 1142 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_239 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (239 : ℕ) / 2)) - ((-480779/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (239 : ℕ) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24569949/50000000) (δ := 71389/2500000000) 1142 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_240 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (240 : ℕ) / 2)) - ((4568381/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (240 : ℕ) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10463937/100000000) (δ := 71389/2500000000) 1142 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_241 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (241 : ℕ) / 2)) - ((-587361/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (241 : ℕ) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 69819387/100000000) (δ := 71389/2500000000) 1142 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_242 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (242 : ℕ) / 2)) - ((4302623/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (242 : ℕ) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14075163/50000000) (δ := 11423/400000000) 1142 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_243 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (243 : ℕ) / 2)) - ((3355383/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (243 : ℕ) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7678873/25000000) (δ := 71407/2500000000) 1142 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_244 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (244 : ℕ) / 2)) - ((-9081261/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (244 : ℕ) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67739571/100000000) (δ := 4461/156250000) 1142 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_245 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (245 : ℕ) / 2)) - ((372317/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (245 : ℕ) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1871107/20000000) (δ := 17847/312500000) 1142 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_246 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (246 : ℕ) / 2)) - ((-1858619/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (246 : ℕ) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48791537/100000000) (δ := 285699/10000000000) 1142 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_247 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (247 : ℕ) / 2)) - ((-1074553/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (247 : ℕ) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12594319/25000000) (δ := 285571/10000000000) 1142 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_248 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (248 : ℕ) / 2)) - ((4788383/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (248 : ℕ) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3649717/50000000) (δ := 285571/10000000000) 1142 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_249 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (249 : ℕ) / 2)) - ((-8515539/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log (249 : ℕ) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (249 : ℕ) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64743461/100000000) (δ := 4463/156250000) 1142 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_250 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (250 : ℕ) / 2)) - ((206517/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (250 : ℕ) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1097517/3125000) (δ := 7139/250000000) 1142 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_251 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (251 : ℕ) / 2)) - ((40081/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log (251 : ℕ) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (251 : ℕ) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2733157/12500000) (δ := 7139/250000000) 1142 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_252 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (252 : ℕ) / 2)) - ((-9999943/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log (252 : ℕ) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (252 : ℕ) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -78455549/100000000) (δ := 57103/2000000000) 1142 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_253 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (253 : ℕ) / 2)) - ((1598971/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log (253 : ℕ) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (253 : ℕ) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21920839/100000000) (δ := 57103/2000000000) 1142 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_254 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (254 : ℕ) / 2)) - ((242391/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log (254 : ℕ) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (254 : ℕ) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34391181/100000000) (δ := 57103/2000000000) 1142 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_255 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (255 : ℕ) / 2)) - ((-1110077/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log (255 : ℕ) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (255 : ℕ) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33298847/50000000) (δ := 285587/10000000000) 1142 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_256 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (256 : ℕ) / 2)) - ((9093527/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log (256 : ℕ) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (256 : ℕ) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2681693/25000000) (δ := 17851/625000000) 1142 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_257 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (257 : ℕ) / 2)) - ((-448617/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log (257 : ℕ) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (257 : ℕ) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44925743/100000000) (δ := 17851/625000000) 1142 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_258 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (258 : ℕ) / 2)) - ((-3212977/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log (258 : ℕ) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (258 : ℕ) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56716927/100000000) (δ := 57109/2000000000) 1142 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_259 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (259 : ℕ) / 2)) - ((9982147/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log (259 : ℕ) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (259 : ℕ) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1494089/100000000) (δ := 142829/5000000000) 1142 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_260 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (260 : ℕ) / 2)) - ((-5395021/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log (260 : ℕ) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (260 : ℕ) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53516051/100000000) (δ := 142829/5000000000) 1142 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_261 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (261 : ℕ) / 2)) - ((-1853637/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log (261 : ℕ) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (261 : ℕ) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6095589/12500000) (δ := 28553/1000000000) 1142 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_262 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (262 : ℕ) / 2)) - ((2432461/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log (262 : ℕ) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (262 : ℕ) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1164863/20000000) (δ := 856673/10000000000) 1142 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_263 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (263 : ℕ) / 2)) - ((-7429057/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log (263 : ℕ) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (263 : ℕ) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 470351/781250) (δ := 28553/1000000000) 1142 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_264 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (264 : ℕ) / 2)) - ((-683799/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log (264 : ℕ) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (264 : ℕ) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10674913/25000000) (δ := 428301/5000000000) 1142 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_265 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (265 : ℕ) / 2)) - ((1125127/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log (265 : ℕ) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (265 : ℕ) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 140873/1250000) (δ := 285601/10000000000) 1142 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_266 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (266 : ℕ) / 2)) - ((-8576431/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log (266 : ℕ) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (266 : ℕ) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16259157/25000000) (δ := 142801/5000000000) 1142 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_267 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (267 : ℕ) / 2)) - ((158171/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log (267 : ℕ) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (267 : ℕ) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19239461/50000000) (δ := 142837/5000000000) 1142 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_268 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (268 : ℕ) / 2)) - ((8279173/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log (268 : ℕ) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (268 : ℕ) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1488531/10000000) (δ := 285529/10000000000) 1142 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_269 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (269 : ℕ) / 2)) - ((-2283183/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log (269 : ℕ) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (269 : ℕ) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 850639/1250000) (δ := 285529/10000000000) 1142 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_270 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (270 : ℕ) / 2)) - ((640279/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log (270 : ℕ) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (270 : ℕ) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18029849/50000000) (δ := 285657/10000000000) 1142 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_271 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (271 : ℕ) / 2)) - ((3923631/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log (271 : ℕ) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (271 : ℕ) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 334271/2000000) (δ := 142773/5000000000) 1142 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_272 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (272 : ℕ) / 2)) - ((-4661739/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log (272 : ℕ) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (272 : ℕ) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6929123/10000000) (δ := 142773/5000000000) 1142 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_273 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (273 : ℕ) / 2)) - ((1540431/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log (273 : ℕ) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (273 : ℕ) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7080687/20000000) (δ := 285617/10000000000) 1142 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_274 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (274 : ℕ) / 2)) - ((3913927/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log (274 : ℕ) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (274 : ℕ) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 671667/4000000) (δ := 285617/10000000000) 1142 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_275 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (275 : ℕ) / 2)) - ((-4624869/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log (275 : ℕ) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (275 : ℕ) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8599259/12500000) (δ := 142793/5000000000) 1142 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_276 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (276 : ℕ) / 2)) - ((558779/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log (276 : ℕ) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (276 : ℕ) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7294033/20000000) (δ := 285689/10000000000) 1142 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_277 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (277 : ℕ) / 2)) - ((4108727/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log (277 : ℕ) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (277 : ℕ) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15158227/100000000) (δ := 142757/5000000000) 1142 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_278 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (278 : ℕ) / 2)) - ((-888097/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log (278 : ℕ) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (278 : ℕ) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66599617/100000000) (δ := 142757/5000000000) 1142 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_279 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (279 : ℕ) / 2)) - ((18283/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log (279 : ℕ) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (279 : ℕ) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39224201/100000000) (δ := 142821/5000000000) 1142 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_280 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (280 : ℕ) / 2)) - ((8897437/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log (280 : ℕ) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (280 : ℕ) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5925161/50000000) (δ := 285561/10000000000) 1142 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_281 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (281 : ℕ) / 2)) - ((-2017171/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (281 : ℕ) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62740697/100000000) (δ := 285561/10000000000) 1142 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_282 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (282 : ℕ) / 2)) - ((-1734589/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log (282 : ℕ) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (282 : ℕ) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21814213/50000000) (δ := 28557/1000000000) 1142 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_283 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (283 : ℕ) / 2)) - ((962129/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log (283 : ℕ) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (283 : ℕ) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6902219/100000000) (δ := 28557/1000000000) 1142 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_284 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (284 : ℕ) / 2)) - ((-6589619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log (284 : ℕ) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (284 : ℕ) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28627927/50000000) (δ := 28557/1000000000) 1142 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_285 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (285 : ℕ) / 2)) - ((-1008311/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log (285 : ℕ) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (285 : ℕ) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49648581/100000000) (δ := 57101/2000000000) 1142 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_286 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (286 : ℕ) / 2)) - ((4999503/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log (286 : ℕ) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (286 : ℕ) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 352461/100000000) (δ := 142849/5000000000) 1142 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_287 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (287 : ℕ) / 2)) - ((-1056519/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log (287 : ℕ) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (287 : ℕ) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 50177921/100000000) (δ := 142849/5000000000) 1142 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_288 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (288 : ℕ) / 2)) - ((-329399/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log (288 : ℕ) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (288 : ℕ) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28625203/50000000) (δ := 35697/1250000000) 1142 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_289 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (289 : ℕ) / 2)) - ((9520843/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log (289 : ℕ) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (289 : ℕ) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7770401/100000000) (δ := 35697/1250000000) 1142 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_290 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (290 : ℕ) / 2)) - ((-453341/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log (290 : ℕ) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (290 : ℕ) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 41539731/100000000) (δ := 285627/10000000000) 1142 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_291 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (291 : ℕ) / 2)) - ((-1768837/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log (291 : ℕ) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (291 : ℕ) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66401069/100000000) (δ := 57111/2000000000) 1142 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_292 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (292 : ℕ) / 2)) - ((3833311/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log (292 : ℕ) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (292 : ℕ) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8714627/50000000) (δ := 57111/2000000000) 1142 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_293 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (293 : ℕ) / 2)) - ((3106071/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log (293 : ℕ) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (293 : ℕ) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7843529/25000000) (δ := 57111/2000000000) 1142 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_294 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (294 : ℕ) / 2)) - ((-4991351/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log (294 : ℕ) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (294 : ℕ) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19267291/25000000) (δ := 3569/125000000) 1142 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_295 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (295 : ℕ) / 2)) - ((1035167/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log (295 : ℕ) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (295 : ℕ) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14298487/50000000) (δ := 3569/125000000) 1142 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_296 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (296 : ℕ) / 2)) - ((7049511/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log (296 : ℕ) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (296 : ℕ) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19711053/100000000) (δ := 285683/10000000000) 1142 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_297 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (297 : ℕ) / 2)) - ((-9100719/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log (297 : ℕ) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (297 : ℕ) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33928173/50000000) (δ := 3569/125000000) 1142 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_298 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (298 : ℕ) / 2)) - ((-98439/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log (298 : ℕ) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (298 : ℕ) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41240729/100000000) (δ := 35699/1250000000) 1142 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_299 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (299 : ℕ) / 2)) - ((9655421/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log (299 : ℕ) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (299 : ℕ) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1645487/25000000) (δ := 285611/10000000000) 1142 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_300 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (300 : ℕ) / 2)) - ((-1127623/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log (300 : ℕ) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (300 : ℕ) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27122373/50000000) (δ := 35699/1250000000) 1142 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_301 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (301 : ℕ) / 2)) - ((-599139/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log (301 : ℕ) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (301 : ℕ) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27665271/50000000) (δ := 285539/10000000000) 1142 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_302 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (302 : ℕ) / 2)) - ((9494463/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log (302 : ℕ) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (302 : ℕ) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3991611/50000000) (δ := 285539/10000000000) 1142 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_303 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (303 : ℕ) / 2)) - ((12567/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log (303 : ℕ) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (303 : ℕ) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39207073/100000000) (δ := 285539/10000000000) 1142 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_304 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (304 : ℕ) / 2)) - ((-9529181/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log (304 : ℕ) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (304 : ℕ) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35418931/50000000) (δ := 57107/2000000000) 1142 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_305 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (305 : ℕ) / 2)) - ((1149741/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log (305 : ℕ) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (305 : ℕ) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11979381/50000000) (δ := 57107/2000000000) 1142 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_306 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (306 : ℕ) / 2)) - ((766431/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log (306 : ℕ) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (306 : ℕ) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22769023/100000000) (δ := 57107/2000000000) 1142 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_307 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (307 : ℕ) / 2)) - ((-9330893/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log (307 : ℕ) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (307 : ℕ) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34671319/50000000) (δ := 57107/2000000000) 1142 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_308 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (308 : ℕ) / 2)) - ((-817003/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log (308 : ℕ) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (308 : ℕ) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8262939/20000000) (δ := 71399/2500000000) 1142 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_309 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (309 : ℕ) / 2)) - ((2451003/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log (309 : ℕ) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (309 : ℕ) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2478859/50000000) (δ := 285607/10000000000) 1142 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_310 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (310 : ℕ) / 2)) - ((-4550367/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log (310 : ℕ) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (310 : ℕ) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51080243/100000000) (δ := 285607/10000000000) 1142 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_311 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (311 : ℕ) / 2)) - ((-738039/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log (311 : ℕ) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (311 : ℕ) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60023897/100000000) (δ := 285679/10000000000) 1142 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_312 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (312 : ℕ) / 2)) - ((8430153/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log (312 : ℕ) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (312 : ℕ) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3549573/25000000) (δ := 285679/10000000000) 1142 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_313 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (313 : ℕ) / 2)) - ((613027/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log (313 : ℕ) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (313 : ℕ) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7870427/25000000) (δ := 285679/10000000000) 1142 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_314 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (314 : ℕ) / 2)) - ((-1247679/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log (314 : ℕ) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (314 : ℕ) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77016103/100000000) (δ := 285679/10000000000) 1142 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_315 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (315 : ℕ) / 2)) - ((228537/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log (315 : ℕ) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (315 : ℕ) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34673313/100000000) (δ := 71413/2500000000) 1142 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_316 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (316 : ℕ) / 2)) - ((9118989/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log (316 : ℕ) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (316 : ℕ) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10572727/100000000) (δ := 71413/2500000000) 1142 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_317 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (317 : ℕ) / 2)) - ((-1525251/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log (317 : ℕ) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (317 : ℕ) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5567459/10000000) (δ := 285551/10000000000) 1142 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_318 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (318 : ℕ) / 2)) - ((-6342081/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log (318 : ℕ) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (318 : ℕ) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56444503/100000000) (δ := 14279/500000000) 1142 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_319 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (319 : ℕ) / 2)) - ((446921/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log (319 : ℕ) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (319 : ℕ) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5811929/50000000) (δ := 14279/500000000) 1142 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_320 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (320 : ℕ) / 2)) - ((246081/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log (320 : ℕ) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (320 : ℕ) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33054037/100000000) (δ := 14279/500000000) 1142 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_321 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (321 : ℕ) / 2)) - ((-4996429/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log (321 : ℕ) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (321 : ℕ) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19398723/25000000) (δ := 14279/500000000) 1142 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_322 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (322 : ℕ) / 2)) - ((833319/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log (322 : ℕ) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (322 : ℕ) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1754189/5000000) (δ := 142847/5000000000) 1142 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_323 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (323 : ℕ) / 2)) - ((4666671/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log (323 : ℕ) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (323 : ℕ) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 459007/5000000) (δ := 142847/5000000000) 1142 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_324 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (324 : ℕ) / 2)) - ((-5324433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log (324 : ℕ) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (324 : ℕ) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2665351/5000000) (δ := 142847/5000000000) 1142 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_325 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (325 : ℕ) / 2)) - ((-914371/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log (325 : ℕ) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (325 : ℕ) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59782773/100000000) (δ := 142783/5000000000) 1142 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_326 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (326 : ℕ) / 2)) - ((8038333/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log (326 : ℕ) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (326 : ℕ) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7963559/50000000) (δ := 142783/5000000000) 1142 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_327 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (327 : ℕ) / 2)) - ((2215359/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log (327 : ℕ) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (327 : ℕ) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1737147/6250000) (δ := 142783/5000000000) 1142 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_328 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (328 : ℕ) / 2)) - ((-4796519/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log (328 : ℕ) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (328 : ℕ) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8922883/12500000) (δ := 285637/10000000000) 1142 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_329 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (329 : ℕ) / 2)) - ((-237211/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log (329 : ℕ) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (329 : ℕ) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -42242041/100000000) (δ := 57113/2000000000) 1142 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_330 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (330 : ℕ) / 2)) - ((199813/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log (330 : ℕ) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (330 : ℕ) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1081157/100000000) (δ := 142819/5000000000) 1142 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_331 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (331 : ℕ) / 2)) - ((-397583/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log (331 : ℕ) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (331 : ℕ) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 345883/781250) (δ := 57113/2000000000) 1142 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_332 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (332 : ℕ) / 2)) - ((-2346879/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log (332 : ℕ) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (332 : ℕ) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17436161/25000000) (δ := 285693/10000000000) 1142 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_333 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (333 : ℕ) / 2)) - ((4779269/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log (333 : ℕ) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (333 : ℕ) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26812581/100000000) (δ := 28551/1000000000) 1142 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_334 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (334 : ℕ) / 2)) - ((4011553/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log (334 : ℕ) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (334 : ℕ) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7995503/50000000) (δ := 285693/10000000000) 1142 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_335 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (335 : ℕ) / 2)) - ((-7003627/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log (335 : ℕ) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (335 : ℕ) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29333773/50000000) (δ := 285693/10000000000) 1142 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_336 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (336 : ℕ) / 2)) - ((-192527/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log (336 : ℕ) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (336 : ℕ) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55864021/100000000) (δ := 142791/5000000000) 1142 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_337 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (337 : ℕ) / 2)) - ((8589079/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log (337 : ℕ) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (337 : ℕ) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1680197/12500000) (δ := 142791/5000000000) 1142 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_338 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (338 : ℕ) / 2)) - ((2023467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log (338 : ℕ) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (338 : ℕ) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28853821/100000000) (δ := 285621/10000000000) 1142 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_339 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (339 : ℕ) / 2)) - ((-1193973/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log (339 : ℕ) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (339 : ℕ) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35513227/50000000) (δ := 142791/5000000000) 1142 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_340 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (340 : ℕ) / 2)) - ((-1883191/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log (340 : ℕ) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (340 : ℕ) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22003083/50000000) (δ := 285653/10000000000) 1142 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_341 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (341 : ℕ) / 2)) - ((9965297/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log (341 : ℕ) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (341 : ℕ) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1041673/50000000) (δ := 285653/10000000000) 1142 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_342 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (342 : ℕ) / 2)) - ((-89641/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log (342 : ℕ) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (342 : ℕ) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4964767/12500000) (δ := 5711/200000000) 1142 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_343 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (343 : ℕ) / 2)) - ((-993477/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log (343 : ℕ) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (343 : ℕ) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75682779/100000000) (δ := 11421/400000000) 1142 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_344 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (344 : ℕ) / 2)) - ((2043311/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log (344 : ℕ) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (344 : ℕ) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34125399/100000000) (δ := 11421/400000000) 1142 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_345 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (345 : ℕ) / 2)) - ((9575309/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log (345 : ℕ) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (345 : ℕ) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7312071/100000000) (δ := 11421/400000000) 1142 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_346 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (346 : ℕ) / 2)) - ((-3656507/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log (346 : ℕ) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (346 : ℕ) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48628203/100000000) (δ := 142839/5000000000) 1142 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_347 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (347 : ℕ) / 2)) - ((-562387/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log (347 : ℕ) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (347 : ℕ) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67253779/100000000) (δ := 285597/10000000000) 1142 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_348 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (348 : ℕ) / 2)) - ((1000369/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log (348 : ℕ) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (348 : ℕ) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6543653/25000000) (δ := 142803/5000000000) 1142 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_349 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (349 : ℕ) / 2)) - ((2075263/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log (349 : ℕ) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (349 : ℕ) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14787501/100000000) (δ := 285597/10000000000) 1142 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_350 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (350 : ℕ) / 2)) - ((-6087221/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log (350 : ℕ) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (350 : ℕ) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 55631131/100000000) (δ := 285597/10000000000) 1142 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_351 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (351 : ℕ) / 2)) - ((-1891379/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log (351 : ℕ) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (351 : ℕ) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60720499/100000000) (δ := 285669/10000000000) 1142 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_352 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (352 : ℕ) / 2)) - ((1387113/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log (352 : ℕ) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (352 : ℕ) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1256847/6250000) (δ := 142767/5000000000) 1142 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_353 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (353 : ℕ) / 2)) - ((6855133/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log (353 : ℕ) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (353 : ℕ) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5096799/25000000) (δ := 285669/10000000000) 1142 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_354 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (354 : ℕ) / 2)) - ((-7578383/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log (354 : ℕ) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (354 : ℕ) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60769743/100000000) (δ := 142767/5000000000) 1142 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_355 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (355 : ℕ) / 2)) - ((-48571/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log (355 : ℕ) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (355 : ℕ) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5604297/10000000) (δ := 285663/10000000000) 1142 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_356 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (356 : ℕ) / 2)) - ((321911/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log (356 : ℕ) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (356 : ℕ) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3177479/20000000) (δ := 285663/10000000000) 1142 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_357 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (357 : ℕ) / 2)) - ((1421159/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log (357 : ℕ) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (357 : ℕ) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1207699/5000000) (δ := 285663/10000000000) 1142 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_358 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (358 : ℕ) / 2)) - ((-8374301/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log (358 : ℕ) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (358 : ℕ) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6408401/10000000) (δ := 285663/10000000000) 1142 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_359 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (359 : ℕ) / 2)) - ((-5280317/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log (359 : ℕ) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (359 : ℕ) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53176937/100000000) (δ := 71403/2500000000) 1142 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_360 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (360 : ℕ) / 2)) - ((4291813/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log (360 : ℕ) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (360 : ℕ) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1346817/10000000) (δ := 285591/10000000000) 1142 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_361 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (361 : ℕ) / 2)) - ((1254387/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log (361 : ℕ) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (361 : ℕ) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26129253/100000000) (δ := 71403/2500000000) 1142 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_362 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (362 : ℕ) / 2)) - ((-347749/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log (362 : ℕ) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (362 : ℕ) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13123637/20000000) (δ := 285591/10000000000) 1142 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_363 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (363 : ℕ) / 2)) - ((-153237/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log (363 : ℕ) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (363 : ℕ) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -203447/390625) (δ := 71421/2500000000) 1142 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_364 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (364 : ℕ) / 2)) - ((871533/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log (364 : ℕ) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (364 : ℕ) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12811907/100000000) (δ := 71421/2500000000) 1142 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_365 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (365 : ℕ) / 2)) - ((4940433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log (365 : ℕ) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (365 : ℕ) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5270311/20000000) (δ := 285519/10000000000) 1142 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_366 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (366 : ℕ) / 2)) - ((-8651863/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log (366 : ℕ) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (366 : ℕ) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13081591/20000000) (δ := 285519/10000000000) 1142 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_367 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (367 : ℕ) / 2)) - ((-5125031/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log (367 : ℕ) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (367 : ℕ) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2636117/5000000) (δ := 71389/2500000000) 1142 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_368 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (368 : ℕ) / 2)) - ((4249119/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log (368 : ℕ) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (368 : ℕ) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6939319/50000000) (δ := 285647/10000000000) 1142 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_369 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (369 : ℕ) / 2)) - ((1362563/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log (369 : ℕ) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (369 : ℕ) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2485943/10000000) (δ := 71389/2500000000) 1142 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_370 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (370 : ℕ) / 2)) - ((-4121417/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log (370 : ℕ) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (370 : ℕ) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6349329/10000000) (δ := 71389/2500000000) 1142 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_371 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (371 : ℕ) / 2)) - ((-5903791/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log (371 : ℕ) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (371 : ℕ) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27529059/50000000) (δ := 11423/400000000) 1142 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_372 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (372 : ℕ) / 2)) - ((3933637/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log (372 : ℕ) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (372 : ℕ) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16632673/100000000) (δ := 11423/400000000) 1142 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_373 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (373 : ℕ) / 2)) - ((6466593/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log (373 : ℕ) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (373 : ℕ) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2711249/12500000) (δ := 11423/400000000) 1142 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_374 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (374 : ℕ) / 2)) - ((-229661/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log (374 : ℕ) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (374 : ℕ) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1198169/2000000) (δ := 71407/2500000000) 1142 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_375 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (375 : ℕ) / 2)) - ((-1422549/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log (375 : ℕ) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (375 : ℕ) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1181053/2000000) (δ := 285699/10000000000) 1142 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_376 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (376 : ℕ) / 2)) - ((6663631/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log (376 : ℕ) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (376 : ℕ) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10518449/50000000) (δ := 4461/156250000) 1142 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_377 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (377 : ℕ) / 2)) - ((1951611/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log (377 : ℕ) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (377 : ℕ) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8438751/50000000) (δ := 4461/156250000) 1142 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_378 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (378 : ℕ) / 2)) - ((-5784953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log (378 : ℕ) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (378 : ℕ) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54691977/100000000) (δ := 4461/156250000) 1142 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_379 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (379 : ℕ) / 2)) - ((-170009/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log (379 : ℕ) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (379 : ℕ) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32335839/50000000) (δ := 285571/10000000000) 1142 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_380 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (380 : ℕ) / 2)) - ((586643/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log (380 : ℕ) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (380 : ℕ) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27057053/100000000) (δ := 285571/10000000000) 1142 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_381 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (381 : ℕ) / 2)) - ((571097/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log (381 : ℕ) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (381 : ℕ) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5229537/50000000) (δ := 4463/156250000) 1142 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_382 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (382 : ℕ) / 2)) - ((-3375651/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log (382 : ℕ) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (382 : ℕ) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11969533/25000000) (δ := 285571/10000000000) 1142 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_383 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (383 : ℕ) / 2)) - ((-9647517/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log (383 : ℕ) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (383 : ℕ) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -561581/781250) (δ := 285643/10000000000) 1142 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_384 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (384 : ℕ) / 2)) - ((458493/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log (384 : ℕ) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (384 : ℕ) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17329439/50000000) (δ := 285643/10000000000) 1142 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_385 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (385 : ℕ) / 2)) - ((9951329/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log (385 : ℕ) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (385 : ℕ) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1233771/50000000) (δ := 285643/10000000000) 1142 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_386 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (386 : ℕ) / 2)) - ((-11349/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log (386 : ℕ) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (386 : ℕ) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9874223/25000000) (δ := 285643/10000000000) 1142 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_387 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (387 : ℕ) / 2)) - ((-9964431/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log (387 : ℕ) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (387 : ℕ) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76430599/100000000) (δ := 7139/250000000) 1142 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_388 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (388 : ℕ) / 2)) - ((-180589/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log (388 : ℕ) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (388 : ℕ) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -43809541/100000000) (δ := 57103/2000000000) 1142 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_389 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (389 : ℕ) / 2)) - ((480163/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log (389 : ℕ) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (389 : ℕ) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7065691/100000000) (δ := 57103/2000000000) 1142 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_390 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (390 : ℕ) / 2)) - ((3778181/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log (390 : ℕ) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (390 : ℕ) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3697993/12500000) (δ := 57103/2000000000) 1142 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_391 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (391 : ℕ) / 2)) - ((-4397423/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log (391 : ℕ) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (391 : ℕ) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16534841/25000000) (δ := 57103/2000000000) 1142 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_392 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (392 : ℕ) / 2)) - ((-5714807/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log (392 : ℕ) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (392 : ℕ) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13619409/25000000) (δ := 285587/10000000000) 1142 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_393 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (393 : ℕ) / 2)) - ((7489557/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log (393 : ℕ) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (393 : ℕ) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18107791/100000000) (δ := 285587/10000000000) 1142 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_394 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (394 : ℕ) / 2)) - ((7473241/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log (394 : ℕ) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (394 : ℕ) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9084633/50000000) (δ := 17851/625000000) 1142 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_395 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (395 : ℕ) / 2)) - ((-2837001/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log (395 : ℕ) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (395 : ℕ) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 424637/781250) (δ := 17851/625000000) 1142 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_396 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (396 : ℕ) / 2)) - ((-1110859/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log (396 : ℕ) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (396 : ℕ) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66631759/100000000) (δ := 57109/2000000000) 1142 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_397 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (397 : ℕ) / 2)) - ((3387499/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log (397 : ℕ) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (397 : ℕ) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30630209/100000000) (δ := 57109/2000000000) 1142 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_398 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (398 : ℕ) / 2)) - ((9777563/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log (398 : ℕ) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (398 : ℕ) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1320709/25000000) (δ := 57109/2000000000) 1142 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_399 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (399 : ℕ) / 2)) - ((-733187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log (399 : ℕ) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (399 : ℕ) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 41104521/100000000) (δ := 57109/2000000000) 1142 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_400 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (400 : ℕ) / 2)) - ((-9976793/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log (400 : ℕ) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (400 : ℕ) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38418137/50000000) (δ := 142829/5000000000) 1142 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_401 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (401 : ℕ) / 2)) - ((-423193/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log (401 : ℕ) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (401 : ℕ) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2787507/6250000) (δ := 285673/10000000000) 1142 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_402 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (402 : ℕ) / 2)) - ((4676179/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log (402 : ℕ) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (402 : ℕ) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9046797/100000000) (δ := 285673/10000000000) 1142 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_403 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (403 : ℕ) / 2)) - ((2458403/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log (403 : ℕ) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (403 : ℕ) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26419441/100000000) (δ := 28553/1000000000) 1142 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_404 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (404 : ℕ) / 2)) - ((-1960011/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log (404 : ℕ) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (404 : ℕ) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61797173/100000000) (δ := 285673/10000000000) 1142 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_405 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (405 : ℕ) / 2)) - ((-3685861/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log (405 : ℕ) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (405 : ℕ) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14997951/25000000) (δ := 142801/5000000000) 1142 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_406 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (406 : ℕ) / 2)) - ((5474109/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log (406 : ℕ) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (406 : ℕ) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24788227/100000000) (δ := 285601/10000000000) 1142 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_407 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (407 : ℕ) / 2)) - ((9158683/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log (407 : ℕ) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (407 : ℕ) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10328273/100000000) (δ := 285601/10000000000) 1142 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_408 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (408 : ℕ) / 2)) - ((-1205837/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log (408 : ℕ) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (408 : ℕ) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45359123/100000000) (δ := 285601/10000000000) 1142 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_409 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (409 : ℕ) / 2)) - ((-4987551/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log (409 : ℕ) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (409 : ℕ) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76775309/100000000) (δ := 142837/5000000000) 1142 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_410 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (410 : ℕ) / 2)) - ((-528183/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log (410 : ℕ) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (410 : ℕ) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41915759/100000000) (δ := 142837/5000000000) 1142 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_411 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (411 : ℕ) / 2)) - ((9594879/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log (411 : ℕ) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (411 : ℕ) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -446277/6250000) (δ := 285529/10000000000) 1142 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_412 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (412 : ℕ) / 2)) - ((4518397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log (412 : ℕ) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (412 : ℕ) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13774623/50000000) (δ := 142837/5000000000) 1142 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_413 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (413 : ℕ) / 2)) - ((-3964007/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log (413 : ℕ) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (413 : ℕ) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62154701/100000000) (δ := 142837/5000000000) 1142 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_414 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (414 : ℕ) / 2)) - ((-3740833/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log (414 : ℕ) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (414 : ℕ) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1887571/3125000) (δ := 142773/5000000000) 1142 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_415 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (415 : ℕ) / 2)) - ((1015033/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log (415 : ℕ) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (415 : ℕ) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25962407/100000000) (δ := 142773/5000000000) 1142 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_416 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (416 : ℕ) / 2)) - ((9441703/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log (416 : ℕ) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (416 : ℕ) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1678647/20000000) (δ := 285657/10000000000) 1142 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_417 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (417 : ℕ) / 2)) - ((-1354861/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log (417 : ℕ) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (417 : ℕ) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4266751/10000000) (δ := 285657/10000000000) 1142 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_418 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (418 : ℕ) / 2)) - ((-9977407/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log (418 : ℕ) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (418 : ℕ) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7685899/10000000) (δ := 285657/10000000000) 1142 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_419 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (419 : ℕ) / 2)) - ((-337779/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log (419 : ℕ) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (419 : ℕ) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4611053/10000000) (δ := 142793/5000000000) 1142 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_420 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (420 : ℕ) / 2)) - ((1770959/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log (420 : ℕ) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (420 : ℕ) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2416357/20000000) (δ := 142793/5000000000) 1142 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_421 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (421 : ℕ) / 2)) - ((801607/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log (421 : ℕ) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (421 : ℕ) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21865593/100000000) (δ := 285617/10000000000) 1142 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_422 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (422 : ℕ) / 2)) - ((-1529877/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log (422 : ℕ) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (422 : ℕ) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5573303/10000000) (δ := 142793/5000000000) 1142 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_423 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (423 : ℕ) / 2)) - ((-9051043/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log (423 : ℕ) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (423 : ℕ) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16890133/25000000) (δ := 285689/10000000000) 1142 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_424 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (424 : ℕ) / 2)) - ((1074929/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log (424 : ℕ) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (424 : ℕ) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1354119/4000000) (δ := 142757/5000000000) 1142 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_425 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (425 : ℕ) / 2)) - ((4999797/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log (425 : ℕ) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (425 : ℕ) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -225357/100000000) (δ := 285689/10000000000) 1142 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_426 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (426 : ℕ) / 2)) - ((1178051/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log (426 : ℕ) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (426 : ℕ) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8330937/25000000) (δ := 285689/10000000000) 1142 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_427 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (427 : ℕ) / 2)) - ((-4458251/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log (427 : ℕ) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (427 : ℕ) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3339717/5000000) (δ := 142757/5000000000) 1142 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_428 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (428 : ℕ) / 2)) - ((-6480257/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log (428 : ℕ) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (428 : ℕ) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -711183/1250000) (δ := 285561/10000000000) 1142 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_429 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (429 : ℕ) / 2)) - ((5872123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log (429 : ℕ) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (429 : ℕ) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4715929/20000000) (δ := 285561/10000000000) 1142 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_430 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (430 : ℕ) / 2)) - ((4631597/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log (430 : ℕ) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (430 : ℕ) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9656837/100000000) (δ := 142821/5000000000) 1142 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_431 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (431 : ℕ) / 2)) - ((-1413213/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log (431 : ℕ) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (431 : ℕ) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42814807/100000000) (δ := 142821/5000000000) 1142 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_432 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (432 : ℕ) / 2)) - ((-9944181/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log (432 : ℕ) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (432 : ℕ) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 474357/625000) (δ := 285561/10000000000) 1142 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_433 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (433 : ℕ) / 2)) - ((-3487509/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log (433 : ℕ) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (433 : ℕ) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24087929/50000000) (δ := 28557/1000000000) 1142 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_434 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (434 : ℕ) / 2)) - ((8197331/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log (434 : ℕ) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (434 : ℕ) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -952893/6250000) (δ := 28557/1000000000) 1142 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_435 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (435 : ℕ) / 2)) - ((3810309/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log (435 : ℕ) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (435 : ℕ) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 140861/800000) (δ := 285633/10000000000) 1142 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_436 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (436 : ℕ) / 2)) - ((-4301319/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log (436 : ℕ) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (436 : ℕ) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1259647/2500000) (δ := 285633/10000000000) 1142 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_437 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (437 : ℕ) / 2)) - ((-4917467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log (437 : ℕ) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (437 : ℕ) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18497789/25000000) (δ := 142849/5000000000) 1142 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_438 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (438 : ℕ) / 2)) - ((-417803/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log (438 : ℕ) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (438 : ℕ) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41361361/100000000) (δ := 142849/5000000000) 1142 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_439 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (439 : ℕ) / 2)) - ((4692927/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log (439 : ℕ) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (439 : ℕ) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8807223/100000000) (δ := 57101/2000000000) 1142 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_440 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (440 : ℕ) / 2)) - ((5841959/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log (440 : ℕ) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (440 : ℕ) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5918171/25000000) (δ := 142849/5000000000) 1142 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_441 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (441 : ℕ) / 2)) - ((-622817/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log (441 : ℕ) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (441 : ℕ) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28039181/50000000) (δ := 57101/2000000000) 1142 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_442 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (442 : ℕ) / 2)) - ((-9230517/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log (442 : ℕ) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (442 : ℕ) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17167099/25000000) (δ := 285627/10000000000) 1142 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_443 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (443 : ℕ) / 2)) - ((142767/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log (443 : ℕ) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (443 : ℕ) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36408323/100000000) (δ := 35697/1250000000) 1142 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_444 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (444 : ℕ) / 2)) - ((49289/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log (444 : ℕ) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (444 : ℕ) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4221053/100000000) (δ := 35697/1250000000) 1142 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_445 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (445 : ℕ) / 2)) - ((109879/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log (445 : ℕ) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (445 : ℕ) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13946707/50000000) (δ := 285627/10000000000) 1142 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_446 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (446 : ℕ) / 2)) - ((-7356759/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log (446 : ℕ) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (446 : ℕ) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59936507/100000000) (δ := 35697/1250000000) 1142 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_447 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (447 : ℕ) / 2)) - ((-8604321/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log (447 : ℕ) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (447 : ℕ) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16293209/25000000) (δ := 57111/2000000000) 1142 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_448 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (448 : ℕ) / 2)) - ((1188011/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log (448 : ℕ) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (448 : ℕ) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33272493/100000000) (δ := 17853/625000000) 1142 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_449 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (449 : ℕ) / 2)) - ((4991651/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log (449 : ℕ) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (449 : ℕ) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1444953/100000000) (δ := 17853/625000000) 1142 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_450 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (450 : ℕ) / 2)) - ((3506741/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log (450 : ℕ) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (450 : ℕ) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30312639/100000000) (δ := 57111/2000000000) 1142 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_451 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (451 : ℕ) / 2)) - ((-7890217/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log (451 : ℕ) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (451 : ℕ) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15500071/25000000) (δ := 57111/2000000000) 1142 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_452 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (452 : ℕ) / 2)) - ((-4117993/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log (452 : ℕ) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (452 : ℕ) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -63463079/100000000) (δ := 285683/10000000000) 1142 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_453 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (453 : ℕ) / 2)) - ((1449791/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log (453 : ℕ) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (453 : ℕ) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31915329/100000000) (δ := 285683/10000000000) 1142 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_454 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (454 : ℕ) / 2)) - ((9998459/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log (454 : ℕ) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (454 : ℕ) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -219477/50000000) (δ := 285683/10000000000) 1142 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_455 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (455 : ℕ) / 2)) - ((651837/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log (455 : ℕ) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (455 : ℕ) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30970329/100000000) (δ := 3569/125000000) 1142 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_456 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (456 : ℕ) / 2)) - ((-199141/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log (456 : ℕ) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (456 : ℕ) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1947177/3125000) (δ := 3569/125000000) 1142 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_457 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (457 : ℕ) / 2)) - ((-2061121/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log (457 : ℕ) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (457 : ℕ) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -63500581/100000000) (δ := 35699/1250000000) 1142 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_458 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (458 : ℕ) / 2)) - ((1376323/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log (458 : ℕ) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (458 : ℕ) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16149143/50000000) (δ := 35699/1250000000) 1142 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_459 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (459 : ℕ) / 2)) - ((499459/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log (459 : ℕ) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (459 : ℕ) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -290771/25000000) (δ := 285611/10000000000) 1142 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_460 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (460 : ℕ) / 2)) - ((1830011/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log (460 : ℕ) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (460 : ℕ) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29902171/100000000) (δ := 285611/10000000000) 1142 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_461 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (461 : ℕ) / 2)) - ((-761273/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log (461 : ℕ) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (461 : ℕ) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60901761/100000000) (δ := 285611/10000000000) 1142 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_462 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (462 : ℕ) / 2)) - ((-53871/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log (462 : ℕ) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (462 : ℕ) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65246801/100000000) (δ := 8927/312500000) 1142 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_463 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (463 : ℕ) / 2)) - ((1942967/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log (463 : ℕ) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (463 : ℕ) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8595349/25000000) (δ := 8927/312500000) 1142 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_464 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (464 : ℕ) / 2)) - ((2474367/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log (464 : ℕ) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (464 : ℕ) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -895771/25000000) (δ := 285539/10000000000) 1142 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_465 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (465 : ℕ) / 2)) - ((1165109/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log (465 : ℕ) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (465 : ℕ) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6787391/25000000) (δ := 8927/312500000) 1142 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_466 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (466 : ℕ) / 2)) - ((-6756223/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log (466 : ℕ) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (466 : ℕ) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 57815119/100000000) (δ := 8927/312500000) 1142 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_467 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (467 : ℕ) / 2)) - ((-576871/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log (467 : ℕ) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (467 : ℕ) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4291539/6250000) (δ := 57107/2000000000) 1142 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_468 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (468 : ℕ) / 2)) - ((227823/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log (468 : ℕ) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (468 : ℕ) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38130399/100000000) (δ := 57107/2000000000) 1142 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_469 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (469 : ℕ) / 2)) - ((4767103/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log (469 : ℕ) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (469 : ℕ) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1915103/25000000) (δ := 71417/2500000000) 1142 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_470 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (470 : ℕ) / 2)) - ((306969/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log (470 : ℕ) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (470 : ℕ) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22743911/100000000) (δ := 57107/2000000000) 1142 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_471 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (471 : ℕ) / 2)) - ((-524871/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log (471 : ℕ) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (471 : ℕ) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13270999/25000000) (δ := 57107/2000000000) 1142 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_472 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (472 : ℕ) / 2)) - ((-4907357/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log (472 : ℕ) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (472 : ℕ) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73719789/100000000) (δ := 285607/10000000000) 1142 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_473 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (473 : ℕ) / 2)) - ((-1687199/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log (473 : ℕ) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (473 : ℕ) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -43508179/100000000) (δ := 285607/10000000000) 1142 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_474 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (474 : ℕ) / 2)) - ((860587/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log (474 : ℕ) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (474 : ℕ) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13359379/100000000) (δ := 285607/10000000000) 1142 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_475 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (475 : ℕ) / 2)) - ((7844377/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log (475 : ℕ) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (475 : ℕ) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16725183/100000000) (δ := 71399/2500000000) 1142 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_476 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (476 : ℕ) / 2)) - ((-2945877/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log (476 : ℕ) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (476 : ℕ) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11686377/25000000) (δ := 71399/2500000000) 1142 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_477 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (477 : ℕ) / 2)) - ((-4986511/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log (477 : ℕ) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (477 : ℕ) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76703023/100000000) (δ := 71399/2500000000) 1142 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_478 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (478 : ℕ) / 2)) - ((-541931/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log (478 : ℕ) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (478 : ℕ) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -50480477/100000000) (δ := 71381/2500000000) 1142 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_479 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (479 : ℕ) / 2)) - ((3389319/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log (479 : ℕ) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (479 : ℕ) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10324291/50000000) (δ := 71381/2500000000) 1142 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_480 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (480 : ℕ) / 2)) - ((291921/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log (480 : ℕ) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (480 : ℕ) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4561679/50000000) (δ := 71381/2500000000) 1142 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_481 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (481 : ℕ) / 2)) - ((17553/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log (481 : ℕ) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (481 : ℕ) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38831061/100000000) (δ := 285679/10000000000) 1142 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_482 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (482 : ℕ) / 2)) - ((-9201079/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log (482 : ℕ) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (482 : ℕ) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8559851/12500000) (δ := 71381/2500000000) 1142 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_483 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (483 : ℕ) / 2)) - ((-7102401/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log (483 : ℕ) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (483 : ℕ) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59015887/100000000) (δ := 285551/10000000000) 1142 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_484 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (484 : ℕ) / 2)) - ((953153/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log (484 : ℕ) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (484 : ℕ) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5898181/20000000) (δ := 71413/2500000000) 1142 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_485 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (485 : ℕ) / 2)) - ((9999993/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log (485 : ℕ) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (485 : ℕ) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7183/25000000) (δ := 285551/10000000000) 1142 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_486 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (486 : ℕ) / 2)) - ((3855463/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log (486 : ℕ) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (486 : ℕ) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29374913/100000000) (δ := 285551/10000000000) 1142 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_487 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (487 : ℕ) / 2)) - ((-7017783/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log (487 : ℕ) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (487 : ℕ) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2348687/4000000) (δ := 71413/2500000000) 1142 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_488 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (488 : ℕ) / 2)) - ((-9292619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log (488 : ℕ) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (488 : ℕ) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1381603/2000000) (δ := 14279/500000000) 1142 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_489 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (489 : ℕ) / 2)) - ((-47141/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log (489 : ℕ) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (489 : ℕ) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1594369/4000000) (δ := 14279/500000000) 1142 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_490 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (490 : ℕ) / 2)) - ((9098503/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log (490 : ℕ) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (490 : ℕ) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10696827/100000000) (δ := 285623/10000000000) 1142 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_491 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (491 : ℕ) / 2)) - ((3704853/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log (491 : ℕ) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (491 : ℕ) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18407043/100000000) (δ := 285623/10000000000) 1142 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_492 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (492 : ℕ) / 2)) - ((-1607163/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log (492 : ℕ) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (492 : ℕ) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23725479/50000000) (δ := 285623/10000000000) 1142 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_493 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (493 : ℕ) / 2)) - ((-311393/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log (493 : ℕ) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (493 : ℕ) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38217459/50000000) (δ := 285623/10000000000) 1142 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_494 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (494 : ℕ) / 2)) - ((-4775973/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log (494 : ℕ) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (494 : ℕ) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10343571/20000000) (δ := 285509/10000000000) 1142 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_495 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (495 : ℕ) / 2)) - ((6105527/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log (495 : ℕ) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (495 : ℕ) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -457019/2000000) (δ := 285509/10000000000) 1142 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_496 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (496 : ℕ) / 2)) - ((9717279/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log (496 : ℕ) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (496 : ℕ) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1191771/20000000) (δ := 285509/10000000000) 1142 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_497 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (497 : ℕ) / 2)) - ((906907/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log (497 : ℕ) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (497 : ℕ) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34710133/100000000) (δ := 142847/5000000000) 1142 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_498 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (498 : ℕ) / 2)) - ((-1644461/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log (498 : ℕ) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (498 : ℕ) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 63402883/100000000) (δ := 142847/5000000000) 1142 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_499 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (499 : ℕ) / 2)) - ((-8577351/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log (499 : ℕ) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (499 : ℕ) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -650411/1000000) (δ := 142783/5000000000) 1142 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_500 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (500 : ℕ) / 2)) - ((224117/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log (500 : ℕ) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (500 : ℕ) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -729251/2000000) (δ := 142783/5000000000) 1142 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_501 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (501 : ℕ) / 2)) - ((9499917/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62166061/20000000 : ℚ) : ℝ) ≤ Real.log (501 : ℕ) / 2 := by
    have h := (log_br_501).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (501 : ℕ) / 2 ≤ ((31083031/10000000 : ℚ) : ℝ) := by
    have h := (log_br_501).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7939673/100000000) (δ := 285637/10000000000) 1142 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_502 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (502 : ℕ) / 2)) - ((425937/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62186001/20000000 : ℚ) : ℝ) ≤ Real.log (502 : ℕ) / 2 := by
    have h := (log_br_502).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (502 : ℕ) / 2 ≤ ((31093001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_502).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20524677/100000000) (δ := 285637/10000000000) 1142 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_503 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (503 : ℕ) / 2)) - ((-3769311/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62205901/20000000 : ℚ) : ℝ) ≤ Real.log (503 : ℕ) / 2 := by
    have h := (log_br_503).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (503 : ℕ) / 2 ≤ ((31102951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_503).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48931927/100000000) (δ := 285637/10000000000) 1142 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_504 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (504 : ℕ) / 2)) - ((-624211/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31112881/10000000 : ℚ) : ℝ) ≤ Real.log (504 : ℕ) / 2 := by
    have h := (log_br_504).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (504 : ℕ) / 2 ≤ ((62225763/20000000 : ℚ) : ℝ) := by
    have h := (log_br_504).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15456701/20000000) (δ := 142783/5000000000) 1142 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_505 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (505 : ℕ) / 2)) - ((-469931/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3890349/1250000 : ℚ) : ℝ) ≤ Real.log (505 : ℕ) / 2 := by
    have h := (log_br_505).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (505 : ℕ) / 2 ≤ ((12449117/4000000 : ℚ) : ℝ) := by
    have h := (log_br_505).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51500223/100000000) (δ := 57113/2000000000) 1142 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_506 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (506 : ℕ) / 2)) - ((2987339/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31132683/10000000 : ℚ) : ℝ) ≤ Real.log (506 : ℕ) / 2 := by
    have h := (log_br_506).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (506 : ℕ) / 2 ≤ ((62265367/20000000 : ℚ) : ℝ) := by
    have h := (log_br_506).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11630709/50000000) (δ := 57113/2000000000) 1142 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_507 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (507 : ℕ) / 2)) - ((9806727/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6228511/2000000 : ℚ) : ℝ) ≤ Real.log (507 : ℕ) / 2 := by
    have h := (log_br_507).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (507 : ℕ) / 2 ≤ ((62285111/20000000 : ℚ) : ℝ) := by
    have h := (log_br_507).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2461571/50000000) (δ := 57113/2000000000) 1142 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_508 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (508 : ℕ) / 2)) - ((1231071/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31152407/10000000 : ℚ) : ℝ) ≤ Real.log (508 : ℕ) / 2 := by
    have h := (log_br_508).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (508 : ℕ) / 2 ≤ ((12460963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_508).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16525301/50000000) (δ := 57113/2000000000) 1142 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_509 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (509 : ℕ) / 2)) - ((-306801/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48691/15625 : ℚ) : ℝ) ≤ Real.log (509 : ℕ) / 2 := by
    have h := (log_br_509).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (509 : ℕ) / 2 ≤ ((62324481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_509).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61123817/100000000) (δ := 57113/2000000000) 1142 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_510 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (510 : ℕ) / 2)) - ((-2278563/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62344107/20000000 : ℚ) : ℝ) ≤ Real.log (510 : ℕ) / 2 := by
    have h := (log_br_510).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (510 : ℕ) / 2 ≤ ((15586027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_510).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67938273/100000000) (δ := 28551/1000000000) 1142 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_511 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (511 : ℕ) / 2)) - ((-883/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12472739/4000000 : ℚ) : ℝ) ≤ Real.log (511 : ℕ) / 2 := by
    have h := (log_br_511).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (511 : ℕ) / 2 ≤ ((3897731/1250000 : ℚ) : ℝ) := by
    have h := (log_br_511).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39976403/100000000) (δ := 28551/1000000000) 1142 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_512 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (512 : ℕ) / 2)) - ((8857477/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31191623/10000000 : ℚ) : ℝ) ≤ Real.log (512 : ℕ) / 2 := by
    have h := (log_br_512).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (512 : ℕ) / 2 ≤ ((62383247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_512).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12067351/100000000) (δ := 285693/10000000000) 1142 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_513 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (513 : ℕ) / 2)) - ((252243/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31201379/10000000 : ℚ) : ℝ) ≤ Real.log (513 : ℕ) / 2 := by
    have h := (log_br_513).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (513 : ℕ) / 2 ≤ ((62402759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_513).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15786029/100000000) (δ := 285693/10000000000) 1142 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_514 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (514 : ℕ) / 2)) - ((-214693/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7802779/2500000 : ℚ) : ℝ) ≤ Real.log (514 : ℕ) / 2 := by
    have h := (log_br_514).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (514 : ℕ) / 2 ≤ ((62422233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_514).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10896291/25000000) (δ := 285693/10000000000) 1142 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_515 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (515 : ℕ) / 2)) - ((-9587191/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62441669/20000000 : ℚ) : ℝ) ≤ Real.log (515 : ℕ) / 2 := by
    have h := (log_br_515).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (515 : ℕ) / 2 ≤ ((6244167/2000000 : ℚ) : ℝ) := by
    have h := (log_br_515).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35665741/50000000) (δ := 28551/1000000000) 1142 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_516 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (516 : ℕ) / 2)) - ((-853423/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62461067/20000000 : ℚ) : ℝ) ≤ Real.log (516 : ℕ) / 2 := by
    have h := (log_br_516).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (516 : ℕ) / 2 ≤ ((15615267/5000000 : ℚ) : ℝ) := by
    have h := (log_br_516).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29028753/50000000) (δ := 285621/10000000000) 1142 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_517 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (517 : ℕ) / 2)) - ((866653/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15620107/5000000 : ℚ) : ℝ) ≤ Real.log (517 : ℕ) / 2 := by
    have h := (log_br_517).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (517 : ℕ) / 2 ≤ ((62480429/20000000 : ℚ) : ℝ) := by
    have h := (log_br_517).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15209839/50000000) (δ := 142791/5000000000) 1142 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_518 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (518 : ℕ) / 2)) - ((4967893/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7812469/2500000 : ℚ) : ℝ) ≤ Real.log (518 : ℕ) / 2 := by
    have h := (log_br_518).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (518 : ℕ) / 2 ≤ ((62499753/20000000 : ℚ) : ℝ) := by
    have h := (log_br_518).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -708667/25000000) (δ := 142791/5000000000) 1142 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_519 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (519 : ℕ) / 2)) - ((344057/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31259519/10000000 : ℚ) : ℝ) ≤ Real.log (519 : ℕ) / 2 := by
    have h := (log_br_519).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (519 : ℕ) / 2 ≤ ((62519039/20000000 : ℚ) : ℝ) := by
    have h := (log_br_519).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24696097/100000000) (δ := 142791/5000000000) 1142 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_520 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (520 : ℕ) / 2)) - ((-987197/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3908643/1250000 : ℚ) : ℝ) ≤ Real.log (520 : ℕ) / 2 := by
    have h := (log_br_520).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (520 : ℕ) / 2 ≤ ((62538289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_520).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3260967/6250000) (δ := 142791/5000000000) 1142 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_521 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (521 : ℕ) / 2)) - ((-9990999/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25023/8000 : ℚ) : ℝ) ≤ Real.log (521 : ℕ) / 2 := by
    have h := (log_br_521).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (521 : ℕ) / 2 ≤ ((62557501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_521).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77479031/100000000) (δ := 5711/200000000) 1142 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_522 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (522 : ℕ) / 2)) - ((-2100123/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2503067/800000 : ℚ) : ℝ) ≤ Real.log (522 : ℕ) / 2 := by
    have h := (log_br_522).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (522 : ℕ) / 2 ≤ ((15644169/5000000 : ℚ) : ℝ) := by
    have h := (log_br_522).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25053359/50000000) (δ := 285653/10000000000) 1142 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_523 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (523 : ℕ) / 2)) - ((6126147/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31297907/10000000 : ℚ) : ℝ) ≤ Real.log (523 : ℕ) / 2 := by
    have h := (log_br_523).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (523 : ℕ) / 2 ≤ ((12519163/4000000 : ℚ) : ℝ) := by
    have h := (log_br_523).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5696449/25000000) (δ := 5711/200000000) 1142 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_524 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (524 : ℕ) / 2)) - ((9839701/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15653729/5000000 : ℚ) : ℝ) ≤ Real.log (524 : ℕ) / 2 := by
    have h := (log_br_524).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (524 : ℕ) / 2 ≤ ((62614917/20000000 : ℚ) : ℝ) := by
    have h := (log_br_524).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4482309/100000000) (δ := 5711/200000000) 1142 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_525 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (525 : ℕ) / 2)) - ((2982277/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31316991/10000000 : ℚ) : ℝ) ≤ Real.log (525 : ℕ) / 2 := by
    have h := (log_br_525).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (525 : ℕ) / 2 ≤ ((62633983/20000000 : ℚ) : ℝ) := by
    have h := (log_br_525).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1981189/6250000) (δ := 5711/200000000) 1142 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_526 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (526 : ℕ) / 2)) - ((-17649/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15663253/5000000 : ℚ) : ℝ) ≤ Real.log (526 : ℕ) / 2 := by
    have h := (log_br_526).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (526 : ℕ) / 2 ≤ ((62653013/20000000 : ℚ) : ℝ) := by
    have h := (log_br_526).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58864349/100000000) (δ := 5711/200000000) 1142 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_527 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (527 : ℕ) / 2)) - ((-9560777/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12534401/4000000 : ℚ) : ℝ) ≤ Real.log (527 : ℕ) / 2 := by
    have h := (log_br_527).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (527 : ℕ) / 2 ≤ ((31336003/10000000 : ℚ) : ℝ) := by
    have h := (log_br_527).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8887847/12500000) (δ := 11421/400000000) 1142 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_528 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (528 : ℕ) / 2)) - ((-474283/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31345481/10000000 : ℚ) : ℝ) ≤ Real.log (528 : ℕ) / 2 := by
    have h := (log_br_528).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (528 : ℕ) / 2 ≤ ((62690963/20000000 : ℚ) : ℝ) := by
    have h := (log_br_528).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44041659/100000000) (δ := 142839/5000000000) 1142 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_529 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (529 : ℕ) / 2)) - ((7768049/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/5000000 : ℚ) : ℝ) ≤ Real.log (529 : ℕ) / 2 := by
    have h := (log_br_529).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (529 : ℕ) / 2 ≤ ((12541977/4000000 : ℚ) : ℝ) := by
    have h := (log_br_529).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2128813/12500000) (δ := 142839/5000000000) 1142 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_530 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (530 : ℕ) / 2)) - ((1152699/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6272877/2000000 : ℚ) : ℝ) ≤ Real.log (530 : ℕ) / 2 := by
    have h := (log_br_530).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (530 : ℕ) / 2 ≤ ((62728771/20000000 : ℚ) : ℝ) := by
    have h := (log_br_530).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9929261/100000000) (δ := 142839/5000000000) 1142 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_531 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (531 : ℕ) / 2)) - ((7771/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3137381/1000000 : ℚ) : ℝ) ≤ Real.log (531 : ℕ) / 2 := by
    have h := (log_br_531).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (531 : ℕ) / 2 ≤ ((62747621/20000000 : ℚ) : ℝ) := by
    have h := (log_br_531).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9209409/25000000) (δ := 142839/5000000000) 1142 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_532 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (532 : ℕ) / 2)) - ((-8288161/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31383217/10000000 : ℚ) : ℝ) ≤ Real.log (532 : ℕ) / 2 := by
    have h := (log_br_532).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (532 : ℕ) / 2 ≤ ((12553287/4000000 : ℚ) : ℝ) := by
    have h := (log_br_532).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 63694621/100000000) (δ := 142839/5000000000) 1142 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_533 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (533 : ℕ) / 2)) - ((-8876727/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31392607/10000000 : ℚ) : ℝ) ≤ Real.log (533 : ℕ) / 2 := by
    have h := (log_br_533).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (533 : ℕ) / 2 ≤ ((12557043/4000000 : ℚ) : ℝ) := by
    have h := (log_br_533).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66576561/100000000) (δ := 285597/10000000000) 1142 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_534 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (534 : ℕ) / 2)) - ((-219819/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31401979/10000000 : ℚ) : ℝ) ≤ Real.log (534 : ℕ) / 2 := by
    have h := (log_br_534).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (534 : ℕ) / 2 ≤ ((62803959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_534).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39819501/100000000) (δ := 285597/10000000000) 1142 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_535 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (535 : ℕ) / 2)) - ((2163941/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62822667/20000000 : ℚ) : ℝ) ≤ Real.log (535 : ℕ) / 2 := by
    have h := (log_br_535).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (535 : ℕ) / 2 ≤ ((15705667/5000000 : ℚ) : ℝ) := by
    have h := (log_br_535).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3278101/25000000) (δ := 142803/5000000000) 1142 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_536 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (536 : ℕ) / 2)) - ((4283937/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62841341/20000000 : ℚ) : ℝ) ≤ Real.log (536 : ℕ) / 2 := by
    have h := (log_br_536).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (536 : ℕ) / 2 ≤ ((31420671/10000000 : ℚ) : ℝ) := by
    have h := (log_br_536).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13544731/100000000) (δ := 142803/5000000000) 1142 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_537 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (537 : ℕ) / 2)) - ((-14109/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3142999/1000000 : ℚ) : ℝ) ≤ Real.log (537 : ℕ) / 2 := by
    have h := (log_br_537).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (537 : ℕ) / 2 ≤ ((62859981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_537).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1254747/3125000) (δ := 285597/10000000000) 1142 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_538 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (538 : ℕ) / 2)) - ((-8901277/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12575717/4000000 : ℚ) : ℝ) ≤ Real.log (538 : ℕ) / 2 := by
    have h := (log_br_538).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (538 : ℕ) / 2 ≤ ((31439293/10000000 : ℚ) : ℝ) := by
    have h := (log_br_538).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66710541/100000000) (δ := 142803/5000000000) 1142 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_539 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (539 : ℕ) / 2)) - ((-1665017/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12579431/4000000 : ℚ) : ℝ) ≤ Real.log (539 : ℕ) / 2 := by
    have h := (log_br_539).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (539 : ℕ) / 2 ≤ ((15724289/5000000 : ℚ) : ℝ) := by
    have h := (log_br_539).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -997819/1562500) (δ := 285669/10000000000) 1142 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_540 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (540 : ℕ) / 2)) - ((186789/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62915691/20000000 : ℚ) : ℝ) ≤ Real.log (540 : ℕ) / 2 := by
    have h := (log_br_540).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (540 : ℕ) / 2 ≤ ((15728923/5000000 : ℚ) : ℝ) := by
    have h := (log_br_540).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9350069/25000000) (δ := 285669/10000000000) 1142 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_541 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (541 : ℕ) / 2)) - ((9049203/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3933387/1250000 : ℚ) : ℝ) ≤ Real.log (541 : ℕ) / 2 := by
    have h := (log_br_541).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (541 : ℕ) / 2 ≤ ((62934193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_541).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10990099/100000000) (δ := 142767/5000000000) 1142 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_542 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (542 : ℕ) / 2)) - ((8168203/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3147633/1000000 : ℚ) : ℝ) ≤ Real.log (542 : ℕ) / 2 := by
    have h := (log_br_542).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (542 : ℕ) / 2 ≤ ((62952661/20000000 : ℚ) : ℝ) := by
    have h := (log_br_542).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15372971/100000000) (δ := 142767/5000000000) 1142 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_543 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (543 : ℕ) / 2)) - ((-241241/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62971093/20000000 : ℚ) : ℝ) ≤ Real.log (543 : ℕ) / 2 := by
    have h := (log_br_543).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (543 : ℕ) / 2 ≤ ((31485547/10000000 : ℚ) : ℝ) := by
    have h := (log_br_543).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 41686079/100000000) (δ := 285669/10000000000) 1142 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_544 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (544 : ℕ) / 2)) - ((-71221/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15747373/5000000 : ℚ) : ℝ) ≤ Real.log (544 : ℕ) / 2 := by
    have h := (log_br_544).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (544 : ℕ) / 2 ≤ ((62989493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_544).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 67950651/100000000) (δ := 142767/5000000000) 1142 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_545 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (545 : ℕ) / 2)) - ((-8109193/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63007857/20000000 : ℚ) : ℝ) ≤ Real.log (545 : ℕ) / 2 := by
    have h := (log_br_545).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (545 : ℕ) / 2 ≤ ((31503929/10000000 : ℚ) : ℝ) := by
    have h := (log_br_545).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3932059/6250000) (δ := 285541/10000000000) 1142 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_546 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (546 : ℕ) / 2)) - ((1576/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63026189/20000000 : ℚ) : ℝ) ≤ Real.log (546 : ℕ) / 2 := by
    have h := (log_br_546).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (546 : ℕ) / 2 ≤ ((6302619/2000000 : ℚ) : ℝ) := by
    have h := (log_br_546).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18372007/50000000) (δ := 285541/10000000000) 1142 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_547 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (547 : ℕ) / 2)) - ((182217/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7880561/2500000 : ℚ) : ℝ) ≤ Real.log (547 : ℕ) / 2 := by
    have h := (log_br_547).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (547 : ℕ) / 2 ≤ ((63044489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_547).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -663887/6250000) (δ := 142831/5000000000) 1142 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_548 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (548 : ℕ) / 2)) - ((4075233/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1970711/625000 : ℚ) : ℝ) ≤ Real.log (548 : ℕ) / 2 := by
    have h := (log_br_548).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (548 : ℕ) / 2 ≤ ((63062753/20000000 : ℚ) : ℝ) := by
    have h := (log_br_548).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3862417/25000000) (δ := 142831/5000000000) 1142 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_549 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (549 : ℕ) / 2)) - ((-881231/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7885123/2500000 : ℚ) : ℝ) ≤ Real.log (549 : ℕ) / 2 := by
    have h := (log_br_549).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (549 : ℕ) / 2 ≤ ((12616197/4000000 : ℚ) : ℝ) := by
    have h := (log_br_549).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5184481/12500000) (δ := 142831/5000000000) 1142 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_550 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (550 : ℕ) / 2)) - ((-1806551/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31549591/10000000 : ℚ) : ℝ) ≤ Real.log (550 : ℕ) / 2 := by
    have h := (log_br_550).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (550 : ℕ) / 2 ≤ ((63099183/20000000 : ℚ) : ℝ) := by
    have h := (log_br_550).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 67453493/100000000) (δ := 142831/5000000000) 1142 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_551 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (551 : ℕ) / 2)) - ((-8288061/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15779337/5000000 : ℚ) : ℝ) ≤ Real.log (551 : ℕ) / 2 := by
    have h := (log_br_551).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (551 : ℕ) / 2 ≤ ((63117349/20000000 : ℚ) : ℝ) := by
    have h := (log_br_551).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31847087/50000000) (δ := 71403/2500000000) 1142 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_552 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (552 : ℕ) / 2)) - ((291667/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1578387/500000 : ℚ) : ℝ) ≤ Real.log (552 : ℕ) / 2 := by
    have h := (log_br_552).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (552 : ℕ) / 2 ≤ ((63135481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_552).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4726343/12500000) (δ := 71403/2500000000) 1142 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_553 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (553 : ℕ) / 2)) - ((2218733/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3157679/1000000 : ℚ) : ℝ) ≤ Real.log (553 : ℕ) / 2 := by
    have h := (log_br_553).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (553 : ℕ) / 2 ≤ ((63153581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_553).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5986497/50000000) (δ := 71403/2500000000) 1142 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_554 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (554 : ℕ) / 2)) - ((851137/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31585823/10000000 : ℚ) : ℝ) ≤ Real.log (554 : ℕ) / 2 := by
    have h := (log_br_554).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (554 : ℕ) / 2 ≤ ((63171647/20000000 : ℚ) : ℝ) := by
    have h := (log_br_554).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13816221/100000000) (δ := 71403/2500000000) 1142 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_555 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (555 : ℕ) / 2)) - ((-116507/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63189681/20000000 : ℚ) : ℝ) ≤ Real.log (555 : ℕ) / 2 := by
    have h := (log_br_555).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (555 : ℕ) / 2 ≤ ((31594841/10000000 : ℚ) : ℝ) := by
    have h := (log_br_555).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39561183/100000000) (δ := 285591/10000000000) 1142 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_556 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (556 : ℕ) / 2)) - ((-8621551/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31603841/10000000 : ℚ) : ℝ) ≤ Real.log (556 : ℕ) / 2 := by
    have h := (log_br_556).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (556 : ℕ) / 2 ≤ ((63207683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_556).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65257611/100000000) (δ := 71403/2500000000) 1142 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_557 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (557 : ℕ) / 2)) - ((-8800643/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15806413/5000000 : ℚ) : ℝ) ≤ Real.log (557 : ℕ) / 2 := by
    have h := (log_br_557).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (557 : ℕ) / 2 ≤ ((63225653/20000000 : ℚ) : ℝ) := by
    have h := (log_br_557).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66169847/100000000) (δ := 285519/10000000000) 1142 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_558 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (558 : ℕ) / 2)) - ((-517717/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63243589/20000000 : ℚ) : ℝ) ≤ Real.log (558 : ℕ) / 2 := by
    have h := (log_br_558).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (558 : ℕ) / 2 ≤ ((6324359/2000000 : ℚ) : ℝ) := by
    have h := (log_br_558).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40564779/100000000) (δ := 71421/2500000000) 1142 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_559 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (559 : ℕ) / 2)) - ((4126069/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31630747/10000000 : ℚ) : ℝ) ≤ Real.log (559 : ℕ) / 2 := by
    have h := (log_br_559).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (559 : ℕ) / 2 ≤ ((12652299/4000000 : ℚ) : ℝ) := by
    have h := (log_br_559).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -937837/6250000) (δ := 285519/10000000000) 1142 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_560 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (560 : ℕ) / 2)) - ((9129533/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63279367/20000000 : ℚ) : ℝ) ≤ Real.log (560 : ℕ) / 2 := by
    have h := (log_br_560).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (560 : ℕ) / 2 ≤ ((7909921/2500000 : ℚ) : ℝ) := by
    have h := (log_br_560).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2627079/25000000) (δ := 71421/2500000000) 1142 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_561 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (561 : ℕ) / 2)) - ((328263/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63297209/20000000 : ℚ) : ℝ) ≤ Real.log (561 : ℕ) / 2 := by
    have h := (log_br_561).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (561 : ℕ) / 2 ≤ ((6329721/2000000 : ℚ) : ℝ) := by
    have h := (log_br_561).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35977771/100000000) (δ := 71421/2500000000) 1142 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_562 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (562 : ℕ) / 2)) - ((-7740469/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31657509/10000000 : ℚ) : ℝ) ≤ Real.log (562 : ℕ) / 2 := by
    have h := (log_br_562).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (562 : ℕ) / 2 ≤ ((63315019/20000000 : ℚ) : ℝ) := by
    have h := (log_br_562).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30700059/50000000) (δ := 285519/10000000000) 1142 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_563 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (563 : ℕ) / 2)) - ((-4730963/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15833199/5000000 : ℚ) : ℝ) ≤ Real.log (563 : ℕ) / 2 := by
    have h := (log_br_563).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (563 : ℕ) / 2 ≤ ((63332797/20000000 : ℚ) : ℝ) := by
    have h := (log_br_563).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3515071/5000000) (δ := 285647/10000000000) 1142 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_564 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (564 : ℕ) / 2)) - ((-451989/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31675271/10000000 : ℚ) : ℝ) ≤ Real.log (564 : ℕ) / 2 := by
    have h := (log_br_564).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (564 : ℕ) / 2 ≤ ((63350543/20000000 : ℚ) : ℝ) := by
    have h := (log_br_564).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8993801/20000000) (δ := 285647/10000000000) 1142 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_565 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (565 : ℕ) / 2)) - ((7058077/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63368257/20000000 : ℚ) : ℝ) ≤ Real.log (565 : ℕ) / 2 := by
    have h := (log_br_565).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (565 : ℕ) / 2 ≤ ((31684129/10000000 : ℚ) : ℝ) := by
    have h := (log_br_565).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9840421/50000000) (δ := 71389/2500000000) 1142 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_566 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (566 : ℕ) / 2)) - ((2438391/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3169297/1000000 : ℚ) : ℝ) ≤ Real.log (566 : ℕ) / 2 := by
    have h := (log_br_566).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (566 : ℕ) / 2 ≤ ((63385941/20000000 : ℚ) : ℝ) := by
    have h := (log_br_566).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 139041/2500000) (δ := 285647/10000000000) 1142 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_567 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (567 : ℕ) / 2)) - ((1669059/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63403593/20000000 : ℚ) : ℝ) ≤ Real.log (567 : ℕ) / 2 := by
    have h := (log_br_567).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (567 : ℕ) / 2 ≤ ((31701797/10000000 : ℚ) : ℝ) := by
    have h := (log_br_567).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15380649/50000000) (δ := 71389/2500000000) 1142 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_568 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (568 : ℕ) / 2)) - ((-6177/10000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31710607/10000000 : ℚ) : ℝ) ≤ Real.log (568 : ℕ) / 2 := by
    have h := (log_br_568).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (568 : ℕ) / 2 ≤ ((12684243/4000000 : ℚ) : ℝ) := by
    have h := (log_br_568).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2236611/4000000) (δ := 285647/10000000000) 1142 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_569 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (569 : ℕ) / 2)) - ((-1243829/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15859701/5000000 : ℚ) : ℝ) ≤ Real.log (569 : ℕ) / 2 := by
    have h := (log_br_569).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (569 : ℕ) / 2 ≤ ((12687761/4000000 : ℚ) : ℝ) := by
    have h := (log_br_569).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9506829/12500000) (δ := 71407/2500000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_570 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (570 : ℕ) / 2)) - ((-2258947/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63456363/20000000 : ℚ) : ℝ) ≤ Real.log (570 : ℕ) / 2 := by
    have h := (log_br_570).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (570 : ℕ) / 2 ≤ ((15864091/5000000 : ℚ) : ℝ) := by
    have h := (log_br_570).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1274729/2500000) (δ := 11423/400000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_571 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (571 : ℕ) / 2)) - ((4059/8000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15868473/5000000 : ℚ) : ℝ) ≤ Real.log (571 : ℕ) / 2 := by
    have h := (log_br_571).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (571 : ℕ) / 2 ≤ ((63473893/20000000 : ℚ) : ℝ) := by
    have h := (log_br_571).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1622907/6250000) (δ := 71407/2500000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_572 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (572 : ℕ) / 2)) - ((9992167/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63491389/20000000 : ℚ) : ℝ) ≤ Real.log (572 : ℕ) / 2 := by
    have h := (log_br_572).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (572 : ℕ) / 2 ≤ ((6349139/2000000 : ℚ) : ℝ) := by
    have h := (log_br_572).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -197909/20000000) (δ := 11423/400000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_573 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (573 : ℕ) / 2)) - ((5752873/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63508857/20000000 : ℚ) : ℝ) ≤ Real.log (573 : ℕ) / 2 := by
    have h := (log_br_573).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (573 : ℕ) / 2 ≤ ((31754429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_573).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 957841/4000000) (δ := 11423/400000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_574 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (574 : ℕ) / 2)) - ((-3733711/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63526293/20000000 : ℚ) : ℝ) ≤ Real.log (574 : ℕ) / 2 := by
    have h := (log_br_574).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (574 : ℕ) / 2 ≤ ((31763147/10000000 : ℚ) : ℝ) := by
    have h := (log_br_574).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9767183/20000000) (δ := 11423/400000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_575 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (575 : ℕ) / 2)) - ((-1226499/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((635437/200000 : ℚ) : ℝ) ≤ Real.log (575 : ℕ) / 2 := by
    have h := (log_br_575).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (575 : ℕ) / 2 ≤ ((63543701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_575).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9210551/12500000) (δ := 71407/2500000000) 1142 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_576 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (576 : ℕ) / 2)) - ((-1396347/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/5000000 : ℚ) : ℝ) ≤ Real.log (576 : ℕ) / 2 := by
    have h := (log_br_576).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (576 : ℕ) / 2 ≤ ((63561077/20000000 : ℚ) : ℝ) := by
    have h := (log_br_576).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11718197/20000000) (δ := 285503/10000000000) 1142 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_577 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (577 : ℕ) / 2)) - ((2159001/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31789211/10000000 : ℚ) : ℝ) ≤ Real.log (577 : ℕ) / 2 := by
    have h := (log_br_577).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (577 : ℕ) / 2 ≤ ((63578423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_577).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3382957/10000000) (δ := 285503/10000000000) 1142 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_578 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (578 : ℕ) / 2)) - ((4671619/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31797869/10000000 : ℚ) : ℝ) ≤ Real.log (578 : ℕ) / 2 := by
    have h := (log_br_578).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (578 : ℕ) / 2 ≤ ((63595739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_578).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -455549/5000000) (δ := 285503/10000000000) 1142 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_579 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (579 : ℕ) / 2)) - ((81237/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1987907/625000 : ℚ) : ℝ) ≤ Real.log (579 : ℕ) / 2 := by
    have h := (log_br_579).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (579 : ℕ) / 2 ≤ ((2544521/800000 : ℚ) : ℝ) := by
    have h := (log_br_579).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3112957/20000000) (δ := 285503/10000000000) 1142 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_580 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (580 : ℕ) / 2)) - ((-92903/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63630281/20000000 : ℚ) : ℝ) ≤ Real.log (580 : ℕ) / 2 := by
    have h := (log_br_580).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (580 : ℕ) / 2 ≤ ((31815141/10000000 : ℚ) : ℝ) := by
    have h := (log_br_580).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40199153/100000000) (δ := 2857/100000000) 1142 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_581 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (581 : ℕ) / 2)) - ((-8525131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63647507/20000000 : ℚ) : ℝ) ≤ Real.log (581 : ℕ) / 2 := by
    have h := (log_br_581).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (581 : ℕ) / 2 ≤ ((15911877/5000000 : ℚ) : ℝ) := by
    have h := (log_br_581).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16197317/25000000) (δ := 2857/100000000) 1142 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_582 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (582 : ℕ) / 2)) - ((-9081609/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((994761/312500 : ℚ) : ℝ) ≤ Real.log (582 : ℕ) / 2 := by
    have h := (log_br_582).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (582 : ℕ) / 2 ≤ ((12732941/4000000 : ℚ) : ℝ) := by
    have h := (log_br_582).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4233853/6250000) (δ := 4463/156250000) 1142 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_583 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (583 : ℕ) / 2)) - ((-789847/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63681871/20000000 : ℚ) : ℝ) ≤ Real.log (583 : ℕ) / 2 := by
    have h := (log_br_583).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (583 : ℕ) / 2 ≤ ((3980117/1250000 : ℚ) : ℝ) := by
    have h := (log_br_583).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8647151/20000000) (δ := 285571/10000000000) 1142 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_584 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (584 : ℕ) / 2)) - ((7311089/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63699009/20000000 : ℚ) : ℝ) ≤ Real.log (584 : ℕ) / 2 := by
    have h := (log_br_584).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (584 : ℕ) / 2 ≤ ((6369901/2000000 : ℚ) : ℝ) := by
    have h := (log_br_584).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -938563/5000000) (δ := 285571/10000000000) 1142 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_585 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (585 : ℕ) / 2)) - ((487277/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31858059/10000000 : ℚ) : ℝ) ≤ Real.log (585 : ℕ) / 2 := by
    have h := (log_br_585).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (585 : ℕ) / 2 ≤ ((63716119/20000000 : ℚ) : ℝ) := by
    have h := (log_br_585).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5651837/100000000) (δ := 4463/156250000) 1142 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_586 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (586 : ℕ) / 2)) - ((3611603/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63733197/20000000 : ℚ) : ℝ) ≤ Real.log (586 : ℕ) / 2 := by
    have h := (log_br_586).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (586 : ℕ) / 2 ≤ ((31866599/10000000 : ℚ) : ℝ) := by
    have h := (log_br_586).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3003211/10000000) (δ := 285571/10000000000) 1142 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_587 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (587 : ℕ) / 2)) - ((-5680217/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7968781/2500000 : ℚ) : ℝ) ≤ Real.log (587 : ℕ) / 2 := by
    have h := (log_br_587).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (587 : ℕ) / 2 ≤ ((63750249/20000000 : ℚ) : ℝ) := by
    have h := (log_br_587).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13593103/25000000) (δ := 4463/156250000) 1142 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_588 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (588 : ℕ) / 2)) - ((-1999973/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63767269/20000000 : ℚ) : ℝ) ≤ Real.log (588 : ℕ) / 2 := by
    have h := (log_br_588).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (588 : ℕ) / 2 ≤ ((6376727/2000000 : ℚ) : ℝ) := by
    have h := (log_br_588).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -78409743/100000000) (δ := 7139/250000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_589 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (589 : ℕ) / 2)) - ((-5607987/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63784261/20000000 : ℚ) : ℝ) ≤ Real.log (589 : ℕ) / 2 := by
    have h := (log_br_589).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (589 : ℕ) / 2 ≤ ((31892131/10000000 : ℚ) : ℝ) := by
    have h := (log_br_589).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54153663/100000000) (δ := 7139/250000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_590 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (590 : ℕ) / 2)) - ((3646847/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2552049/800000 : ℚ) : ℝ) ≤ Real.log (590 : ℕ) / 2 := by
    have h := (log_br_590).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (590 : ℕ) / 2 ≤ ((31900613/10000000 : ℚ) : ℝ) := by
    have h := (log_br_590).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29937553/100000000) (δ := 7139/250000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_591 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (591 : ℕ) / 2)) - ((2433873/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((797727/250000 : ℚ) : ℝ) ≤ Real.log (591 : ℕ) / 2 := by
    have h := (log_br_591).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (591 : ℕ) / 2 ≤ ((63818161/20000000 : ℚ) : ℝ) := by
    have h := (log_br_591).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -144071/2500000) (δ := 285643/10000000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_592 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (592 : ℕ) / 2)) - ((7419521/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31917533/10000000 : ℚ) : ℝ) ≤ Real.log (592 : ℕ) / 2 := by
    have h := (log_br_592).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (592 : ℕ) / 2 ≤ ((63835067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_592).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 734819/4000000) (δ := 285643/10000000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_593 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (593 : ℕ) / 2)) - ((-636763/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31925971/10000000 : ℚ) : ℝ) ≤ Real.log (593 : ℕ) / 2 := by
    have h := (log_br_593).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (593 : ℕ) / 2 ≤ ((12770389/4000000 : ℚ) : ℝ) := by
    have h := (log_br_593).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5307799/12500000) (δ := 10707/125000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_594 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (594 : ℕ) / 2)) - ((-8865503/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63868793/20000000 : ℚ) : ℝ) ≤ Real.log (594 : ℕ) / 2 := by
    have h := (log_br_594).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (594 : ℕ) / 2 ≤ ((31934397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_594).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66515767/100000000) (δ := 7139/250000000) 1142 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_595 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (595 : ℕ) / 2)) - ((-4436089/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31942807/10000000 : ℚ) : ℝ) ≤ Real.log (595 : ℕ) / 2 := by
    have h := (log_br_595).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (595 : ℕ) / 2 ≤ ((12777123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_595).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4159493/6250000) (δ := 57103/2000000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_596 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (596 : ℕ) / 2)) - ((-132069/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31951203/10000000 : ℚ) : ℝ) ≤ Real.log (596 : ℕ) / 2 := by
    have h := (log_br_596).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (596 : ℕ) / 2 ≤ ((63902407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_596).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10645327/25000000) (δ := 57103/2000000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_597 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (597 : ℕ) / 2)) - ((3672147/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63919171/20000000 : ℚ) : ℝ) ≤ Real.log (597 : ℕ) / 2 := by
    have h := (log_br_597).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (597 : ℕ) / 2 ≤ ((15979793/5000000 : ℚ) : ℝ) := by
    have h := (log_br_597).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18649271/100000000) (δ := 35711/1250000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_598 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (598 : ℕ) / 2)) - ((2445257/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63935907/20000000 : ℚ) : ℝ) ≤ Real.log (598 : ℕ) / 2 := by
    have h := (log_br_598).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (598 : ℕ) / 2 ≤ ((15983977/5000000 : ℚ) : ℝ) := by
    have h := (log_br_598).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5241369/100000000) (δ := 35711/1250000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_599 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (599 : ℕ) / 2)) - ((61869/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12790523/4000000 : ℚ) : ℝ) ≤ Real.log (599 : ℕ) / 2 := by
    have h := (log_br_599).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (599 : ℕ) / 2 ≤ ((7994077/2500000 : ℚ) : ℝ) := by
    have h := (log_br_599).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29092039/100000000) (δ := 35711/1250000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_600 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (600 : ℕ) / 2)) - ((-1296837/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3998081/1250000 : ℚ) : ℝ) ≤ Real.log (600 : ℕ) / 2 := by
    have h := (log_br_600).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (600 : ℕ) / 2 ≤ ((63969297/20000000 : ℚ) : ℝ) := by
    have h := (log_br_600).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52904167/100000000) (δ := 57103/2000000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_601 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (601 : ℕ) / 2)) - ((-1246529/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63985949/20000000 : ℚ) : ℝ) ≤ Real.log (601 : ℕ) / 2 := by
    have h := (log_br_601).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (601 : ℕ) / 2 ≤ ((1279719/400000 : ℚ) : ℝ) := by
    have h := (log_br_601).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19169081/25000000) (δ := 35711/1250000000) 1142 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_602 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (602 : ℕ) / 2)) - ((-50093/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32001287/10000000 : ℚ) : ℝ) ≤ Real.log (602 : ℕ) / 2 := by
    have h := (log_br_602).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (602 : ℕ) / 2 ≤ ((2560103/800000 : ℚ) : ℝ) := by
    have h := (log_br_602).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56671121/100000000) (δ := 17851/625000000) 1142 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_603 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (603 : ℕ) / 2)) - ((311241/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64019171/20000000 : ℚ) : ℝ) ≤ Real.log (603 : ℕ) / 2 := by
    have h := (log_br_603).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (603 : ℕ) / 2 ≤ ((16004793/5000000 : ℚ) : ℝ) := by
    have h := (log_br_603).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32978903/100000000) (δ := 285587/10000000000) 1142 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_604 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (604 : ℕ) / 2)) - ((186247/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64035741/20000000 : ℚ) : ℝ) ≤ Real.log (604 : ℕ) / 2 := by
    have h := (log_br_604).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (604 : ℕ) / 2 ≤ ((32017871/10000000 : ℚ) : ℝ) := by
    have h := (log_br_604).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2331307/25000000) (δ := 285587/10000000000) 1142 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_605 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (605 : ℕ) / 2)) - ((4205193/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16013071/5000000 : ℚ) : ℝ) ≤ Real.log (605 : ℕ) / 2 := by
    have h := (log_br_605).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (605 : ℕ) / 2 ≤ ((12810457/4000000 : ℚ) : ℝ) := by
    have h := (log_br_605).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 893119/6250000) (δ := 17851/625000000) 1142 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_606 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (606 : ℕ) / 2)) - ((561641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64068799/20000000 : ℚ) : ℝ) ≤ Real.log (606 : ℕ) / 2 := by
    have h := (log_br_606).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (606 : ℕ) / 2 ≤ ((40043/12500 : ℚ) : ℝ) := by
    have h := (log_br_606).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37865067/100000000) (δ := 285587/10000000000) 1142 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_607 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (607 : ℕ) / 2)) - ((-7740867/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64085287/20000000 : ℚ) : ℝ) ≤ Real.log (607 : ℕ) / 2 := by
    have h := (log_br_607).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (607 : ℕ) / 2 ≤ ((8010661/2500000 : ℚ) : ℝ) := by
    have h := (log_br_607).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61401687/100000000) (δ := 285587/10000000000) 1142 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_608 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (608 : ℕ) / 2)) - ((-193563/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16025437/5000000 : ℚ) : ℝ) ≤ Real.log (608 : ℕ) / 2 := by
    have h := (log_br_608).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (608 : ℕ) / 2 ≤ ((64101749/20000000 : ℚ) : ℝ) := by
    have h := (log_br_608).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18044967/25000000) (δ := 142829/5000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_609 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (609 : ℕ) / 2)) - ((-1845391/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32059091/10000000 : ℚ) : ℝ) ≤ Real.log (609 : ℕ) / 2 := by
    have h := (log_br_609).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (609 : ℕ) / 2 ≤ ((64118183/20000000 : ℚ) : ℝ) := by
    have h := (log_br_609).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -48720333/100000000) (δ := 142829/5000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_610 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (610 : ℕ) / 2)) - ((5301883/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64134589/20000000 : ℚ) : ℝ) ≤ Real.log (610 : ℕ) / 2 := by
    have h := (log_br_610).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (610 : ℕ) / 2 ≤ ((6413459/2000000 : ℚ) : ℝ) := by
    have h := (log_br_610).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25299341/100000000) (δ := 57109/2000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_611 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (611 : ℕ) / 2)) - ((9970619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64150969/20000000 : ℚ) : ℝ) ≤ Real.log (611 : ℕ) / 2 := by
    have h := (log_br_611).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (611 : ℕ) / 2 ≤ ((6415097/2000000 : ℚ) : ℝ) := by
    have h := (log_br_611).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1916891/100000000) (δ := 57109/2000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_612 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (612 : ℕ) / 2)) - ((6546471/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32083661/10000000 : ℚ) : ℝ) ≤ Real.log (612 : ℕ) / 2 := by
    have h := (log_br_612).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (612 : ℕ) / 2 ≤ ((64167323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_612).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21427017/100000000) (δ := 142829/5000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_613 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (613 : ℕ) / 2)) - ((-1084101/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64183649/20000000 : ℚ) : ℝ) ≤ Real.log (613 : ℕ) / 2 := by
    have h := (log_br_613).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (613 : ℕ) / 2 ≤ ((1283673/400000 : ℚ) : ℝ) := by
    have h := (log_br_613).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44733809/100000000) (δ := 57109/2000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_614 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (614 : ℕ) / 2)) - ((-9124721/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64199949/20000000 : ℚ) : ℝ) ≤ Real.log (614 : ℕ) / 2 := by
    have h := (log_br_614).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (614 : ℕ) / 2 ≤ ((1283999/400000 : ℚ) : ℝ) := by
    have h := (log_br_614).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 68002059/100000000) (δ := 57109/2000000000) 1142 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_615 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (615 : ℕ) / 2)) - ((-8738757/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32108111/10000000 : ℚ) : ℝ) ≤ Real.log (615 : ℕ) / 2 := by
    have h := (log_br_615).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (615 : ℕ) / 2 ≤ ((64216223/20000000 : ℚ) : ℝ) := by
    have h := (log_br_615).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32923933/50000000) (δ := 28553/1000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_616 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (616 : ℕ) / 2)) - ((-337503/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64232469/20000000 : ℚ) : ℝ) ≤ Real.log (616 : ℕ) / 2 := by
    have h := (log_br_616).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (616 : ℕ) / 2 ≤ ((6423247/2000000 : ℚ) : ℝ) := by
    have h := (log_br_616).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21327637/50000000) (δ := 285673/10000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_617 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (617 : ℕ) / 2)) - ((7109193/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6424869/2000000 : ℚ) : ℝ) ≤ Real.log (617 : ℕ) / 2 := by
    have h := (log_br_617).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (617 : ℕ) / 2 ≤ ((64248691/20000000 : ℚ) : ℝ) := by
    have h := (log_br_617).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4874949/25000000) (δ := 28553/1000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_618 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (618 : ℕ) / 2)) - ((9895513/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16066221/5000000 : ℚ) : ℝ) ≤ Real.log (618 : ℕ) / 2 := by
    have h := (log_br_618).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (618 : ℕ) / 2 ≤ ((12852977/4000000 : ℚ) : ℝ) := by
    have h := (log_br_618).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3617139/100000000) (δ := 28553/1000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_619 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (619 : ℕ) / 2)) - ((4819843/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16070263/5000000 : ℚ) : ℝ) ≤ Real.log (619 : ℕ) / 2 := by
    have h := (log_br_619).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (619 : ℕ) / 2 ≤ ((64281053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_619).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26696959/100000000) (δ := 28553/1000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_620 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (620 : ℕ) / 2)) - ((-813311/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32148597/10000000 : ℚ) : ℝ) ≤ Real.log (620 : ℕ) / 2 := by
    have h := (log_br_620).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (620 : ℕ) / 2 ≤ ((12859439/4000000 : ℚ) : ℝ) := by
    have h := (log_br_620).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3108729/6250000) (δ := 28553/1000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_621 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (621 : ℕ) / 2)) - ((-1946517/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6431331/2000000 : ℚ) : ℝ) ≤ Real.log (621 : ℕ) / 2 := by
    have h := (log_br_621).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (621 : ℕ) / 2 ≤ ((64313311/20000000 : ℚ) : ℝ) := by
    have h := (log_br_621).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36372627/50000000) (δ := 28553/1000000000) 1142 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_622 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (622 : ℕ) / 2)) - ((-7731797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((321647/100000 : ℚ) : ℝ) ≤ Real.log (622 : ℕ) / 2 := by
    have h := (log_br_622).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (622 : ℕ) / 2 ≤ ((64329401/20000000 : ℚ) : ℝ) := by
    have h := (log_br_622).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3835369/6250000) (δ := 285601/10000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_623 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (623 : ℕ) / 2)) - ((167327/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12869093/4000000 : ℚ) : ℝ) ≤ Real.log (623 : ℕ) / 2 := by
    have h := (log_br_623).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (623 : ℕ) / 2 ≤ ((32172733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_623).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9608279/25000000) (δ := 142801/5000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_624 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (624 : ℕ) / 2)) - ((8129741/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64361503/20000000 : ℚ) : ℝ) ≤ Real.log (624 : ℕ) / 2 := by
    have h := (log_br_624).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (624 : ℕ) / 2 ≤ ((2011297/625000 : ℚ) : ℝ) := by
    have h := (log_br_624).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15538871/100000000) (δ := 142801/5000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_625 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (625 : ℕ) / 2)) - ((9574431/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/5000000 : ℚ) : ℝ) ≤ Real.log (625 : ℕ) / 2 := by
    have h := (log_br_625).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (625 : ℕ) / 2 ≤ ((64377517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_625).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3659843/50000000) (δ := 285601/10000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_626 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (626 : ℕ) / 2)) - ((714181/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64393503/20000000 : ℚ) : ℝ) ≤ Real.log (626 : ℕ) / 2 := by
    have h := (log_br_626).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (626 : ℕ) / 2 ≤ ((2012297/625000 : ℚ) : ℝ) := by
    have h := (log_br_626).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30141129/100000000) (δ := 142801/5000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_627 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (627 : ℕ) / 2)) - ((-2597557/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12881893/4000000 : ℚ) : ℝ) ≤ Real.log (627 : ℕ) / 2 := by
    have h := (log_br_627).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (627 : ℕ) / 2 ≤ ((32204733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_627).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13231721/25000000) (δ := 142801/5000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_628 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (628 : ℕ) / 2)) - ((-4967219/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64425401/20000000 : ℚ) : ℝ) ≤ Real.log (628 : ℕ) / 2 := by
    have h := (log_br_628).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (628 : ℕ) / 2 ≤ ((32212701/10000000 : ℚ) : ℝ) := by
    have h := (log_br_628).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18918881/25000000) (δ := 142801/5000000000) 1142 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_629 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (629 : ℕ) / 2)) - ((-1402073/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2013791/625000 : ℚ) : ℝ) ≤ Real.log (629 : ℕ) / 2 := by
    have h := (log_br_629).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (629 : ℕ) / 2 ≤ ((64441313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_629).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14672789/25000000) (δ := 142837/5000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_630 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (630 : ℕ) / 2)) - ((162341/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32228599/10000000 : ℚ) : ℝ) ≤ Real.log (630 : ℕ) / 2 := by
    have h := (log_br_630).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (630 : ℕ) / 2 ≤ ((64457199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_630).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36013891/100000000) (δ := 142837/5000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_631 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (631 : ℕ) / 2)) - ((8602943/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32236529/10000000 : ℚ) : ℝ) ≤ Real.log (631 : ℕ) / 2 := by
    have h := (log_br_631).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (631 : ℕ) / 2 ≤ ((64473059/20000000 : ℚ) : ℝ) := by
    have h := (log_br_631).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13373741/100000000) (δ := 142837/5000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_632 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (632 : ℕ) / 2)) - ((9326059/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64488893/20000000 : ℚ) : ℝ) ≤ Real.log (632 : ℕ) / 2 := by
    have h := (log_br_632).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (632 : ℕ) / 2 ≤ ((32244447/10000000 : ℚ) : ℝ) := by
    have h := (log_br_632).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9230721/100000000) (δ := 285529/10000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_633 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (633 : ℕ) / 2)) - ((735837/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((503943/156250 : ℚ) : ℝ) ≤ Real.log (633 : ℕ) / 2 := by
    have h := (log_br_633).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (633 : ℕ) / 2 ≤ ((12900941/4000000 : ℚ) : ℝ) := by
    have h := (log_br_633).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7950231/25000000) (δ := 142837/5000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_634 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (634 : ℕ) / 2)) - ((-5667569/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64520489/20000000 : ℚ) : ℝ) ≤ Real.log (634 : ℕ) / 2 := by
    have h := (log_br_634).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (634 : ℕ) / 2 ≤ ((6452049/2000000 : ℚ) : ℝ) := by
    have h := (log_br_634).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54334011/100000000) (δ := 285529/10000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_635 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (635 : ℕ) / 2)) - ((-498833/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8067031/2500000 : ℚ) : ℝ) ≤ Real.log (635 : ℕ) / 2 := by
    have h := (log_br_635).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (635 : ℕ) / 2 ≤ ((64536251/20000000 : ℚ) : ℝ) := by
    have h := (log_br_635).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76831411/100000000) (δ := 856529/10000000000) 1142 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_636 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (636 : ℕ) / 2)) - ((-42171/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12910397/4000000 : ℚ) : ℝ) ≤ Real.log (636 : ℕ) / 2 := by
    have h := (log_br_636).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (636 : ℕ) / 2 ≤ ((32275993/10000000 : ℚ) : ℝ) := by
    have h := (log_br_636).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28892541/50000000) (δ := 285657/10000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_637 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (637 : ℕ) / 2)) - ((389633/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4035481/1250000 : ℚ) : ℝ) ≤ Real.log (637 : ℕ) / 2 := by
    have h := (log_br_637).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (637 : ℕ) / 2 ≤ ((64567697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_637).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35357629/100000000) (δ := 142773/5000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_638 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (638 : ℕ) / 2)) - ((1085621/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32291691/10000000 : ℚ) : ℝ) ≤ Real.log (638 : ℕ) / 2 := by
    have h := (log_br_638).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (638 : ℕ) / 2 ≤ ((64583383/20000000 : ℚ) : ℝ) := by
    have h := (log_br_638).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1620733/12500000) (δ := 142773/5000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_639 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (639 : ℕ) / 2)) - ((2325659/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16149761/5000000 : ℚ) : ℝ) ≤ Real.log (639 : ℕ) / 2 := by
    have h := (log_br_639).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (639 : ℕ) / 2 ≤ ((12919809/4000000 : ℚ) : ℝ) := by
    have h := (log_br_639).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9391641/100000000) (δ := 142773/5000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_640 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (640 : ℕ) / 2)) - ((1488383/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64614681/20000000 : ℚ) : ℝ) ≤ Real.log (640 : ℕ) / 2 := by
    have h := (log_br_640).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (640 : ℕ) / 2 ≤ ((32307341/10000000 : ℚ) : ℝ) := by
    have h := (log_br_640).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15856729/50000000) (δ := 285657/10000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_641 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (641 : ℕ) / 2)) - ((-5557329/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32315147/10000000 : ℚ) : ℝ) ≤ Real.log (641 : ℕ) / 2 := by
    have h := (log_br_641).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (641 : ℕ) / 2 ≤ ((12926059/4000000 : ℚ) : ℝ) := by
    have h := (log_br_641).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6750127/12500000) (δ := 142773/5000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_642 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (642 : ℕ) / 2)) - ((-9958241/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64645883/20000000 : ℚ) : ℝ) ≤ Real.log (642 : ℕ) / 2 := by
    have h := (log_br_642).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (642 : ℕ) / 2 ≤ ((16161471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_642).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76254313/100000000) (δ := 285657/10000000000) 1142 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_643 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (643 : ℕ) / 2)) - ((-6986523/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64661447/20000000 : ℚ) : ℝ) ≤ Real.log (643 : ℕ) / 2 := by
    have h := (log_br_643).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (643 : ℕ) / 2 ≤ ((8082681/2500000 : ℚ) : ℝ) := by
    have h := (log_br_643).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -58607709/100000000) (δ := 285617/10000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_644 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (644 : ℕ) / 2)) - ((283941/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64676987/20000000 : ℚ) : ℝ) ≤ Real.log (644 : ℕ) / 2 := by
    have h := (log_br_644).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (644 : ℕ) / 2 ≤ ((16169247/5000000 : ℚ) : ℝ) := by
    have h := (log_br_644).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36424359/100000000) (δ := 285617/10000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_645 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (645 : ℕ) / 2)) - ((8413551/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64692503/20000000 : ℚ) : ℝ) ≤ Real.log (645 : ℕ) / 2 := by
    have h := (log_br_645).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (645 : ℕ) / 2 ≤ ((8086563/2500000 : ℚ) : ℝ) := by
    have h := (log_br_645).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14275269/100000000) (δ := 285617/10000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_646 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (646 : ℕ) / 2)) - ((4756173/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12941599/4000000 : ℚ) : ℝ) ≤ Real.log (646 : ℕ) / 2 := by
    have h := (log_br_646).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (646 : ℕ) / 2 ≤ ((16176999/5000000 : ℚ) : ℝ) := by
    have h := (log_br_646).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7839561/100000000) (δ := 285617/10000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_647 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (647 : ℕ) / 2)) - ((3653867/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32361731/10000000 : ℚ) : ℝ) ≤ Real.log (647 : ℕ) / 2 := by
    have h := (log_br_647).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (647 : ℕ) / 2 ≤ ((64723463/20000000 : ℚ) : ℝ) := by
    have h := (log_br_647).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29918703/100000000) (δ := 142793/5000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_648 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (648 : ℕ) / 2)) - ((-4862597/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12947781/4000000 : ℚ) : ℝ) ≤ Real.log (648 : ℕ) / 2 := by
    have h := (log_br_648).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (648 : ℕ) / 2 ≤ ((16184727/5000000 : ℚ) : ℝ) := by
    have h := (log_br_648).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51965013/100000000) (δ := 428293/5000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_649 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (649 : ℕ) / 2)) - ((-307313/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64754327/20000000 : ℚ) : ℝ) ≤ Real.log (649 : ℕ) / 2 := by
    have h := (log_br_649).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (649 : ℕ) / 2 ≤ ((8094291/2500000 : ℚ) : ℝ) := by
    have h := (log_br_649).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73978491/100000000) (δ := 285617/10000000000) 1142 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_650 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (650 : ℕ) / 2)) - ((-1533981/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64769723/20000000 : ℚ) : ℝ) ≤ Real.log (650 : ℕ) / 2 := by
    have h := (log_br_650).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (650 : ℕ) / 2 ≤ ((16192431/5000000 : ℚ) : ℝ) := by
    have h := (log_br_650).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7640419/12500000) (δ := 142757/5000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_651 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (651 : ℕ) / 2)) - ((18303/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8098137/2500000 : ℚ) : ℝ) ≤ Real.log (651 : ℕ) / 2 := by
    have h := (log_br_651).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (651 : ℕ) / 2 ≤ ((64785097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_651).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19589197/50000000) (δ := 285689/10000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_652 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (652 : ℕ) / 2)) - ((481747/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12960089/4000000 : ℚ) : ℝ) ≤ Real.log (652 : ℕ) / 2 := by
    have h := (log_br_652).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (652 : ℕ) / 2 ≤ ((32400223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_652).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17267697/100000000) (δ := 142757/5000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_653 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (653 : ℕ) / 2)) - ((2457613/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64815771/20000000 : ℚ) : ℝ) ≤ Real.log (653 : ℕ) / 2 := by
    have h := (log_br_653).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (653 : ℕ) / 2 ≤ ((16203943/5000000 : ℚ) : ℝ) := by
    have h := (log_br_653).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 576271/12500000) (δ := 142757/5000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_654 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (654 : ℕ) / 2)) - ((4904843/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64831073/20000000 : ℚ) : ℝ) ≤ Real.log (654 : ℕ) / 2 := by
    have h := (log_br_654).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (654 : ℕ) / 2 ≤ ((32415537/10000000 : ℚ) : ℝ) := by
    have h := (log_br_654).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26453773/100000000) (δ := 142757/5000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_655 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (655 : ℕ) / 2)) - ((-704147/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4052897/1250000 : ℚ) : ℝ) ≤ Real.log (655 : ℕ) / 2 := by
    have h := (log_br_655).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (655 : ℕ) / 2 ≤ ((64846353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_655).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24132273/50000000) (δ := 285689/10000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_656 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (656 : ℕ) / 2)) - ((-73654/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64861607/20000000 : ℚ) : ℝ) ≤ Real.log (656 : ℕ) / 2 := by
    have h := (log_br_656).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (656 : ℕ) / 2 ≤ ((8107701/2500000 : ℚ) : ℝ) := by
    have h := (log_br_656).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35020529/50000000) (δ := 142757/5000000000) 1142 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_657 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (657 : ℕ) / 2)) - ((-8628809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1621921/500000 : ℚ) : ℝ) ≤ Real.log (657 : ℕ) / 2 := by
    have h := (log_br_657).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (657 : ℕ) / 2 ≤ ((64876841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_657).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65293467/100000000) (δ := 285561/10000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_658 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (658 : ℕ) / 2)) - ((-1716541/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64892049/20000000 : ℚ) : ℝ) ≤ Real.log (658 : ℕ) / 2 := by
    have h := (log_br_658).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (658 : ℕ) / 2 ≤ ((1297841/400000 : ℚ) : ℝ) := by
    have h := (log_br_658).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2179131/5000000) (δ := 142821/5000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_659 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (659 : ℕ) / 2)) - ((51207/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12981447/4000000 : ℚ) : ℝ) ≤ Real.log (659 : ℕ) / 2 := by
    have h := (log_br_659).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (659 : ℕ) / 2 ≤ ((16226809/5000000 : ℚ) : ℝ) := by
    have h := (log_br_659).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4380921/20000000) (δ := 142821/5000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_660 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (660 : ℕ) / 2)) - ((4999731/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32461199/10000000 : ℚ) : ℝ) ≤ Real.log (660 : ℕ) / 2 := by
    have h := (log_br_660).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (660 : ℕ) / 2 ≤ ((64922399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_660).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -129711/50000000) (δ := 285561/10000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_661 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (661 : ℕ) / 2)) - ((1642211/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32468769/10000000 : ℚ) : ℝ) ≤ Real.log (661 : ℕ) / 2 := by
    have h := (log_br_661).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (661 : ℕ) / 2 ≤ ((64937539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_661).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 667279/3125000) (δ := 285561/10000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_662 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (662 : ℕ) / 2)) - ((-72989/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12990531/4000000 : ℚ) : ℝ) ≤ Real.log (662 : ℕ) / 2 := by
    have h := (log_br_662).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (662 : ℕ) / 2 ≤ ((4059541/1250000 : ℚ) : ℝ) := by
    have h := (log_br_662).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8586489/20000000) (δ := 142821/5000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_663 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (663 : ℕ) / 2)) - ((-528727/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64967749/20000000 : ℚ) : ℝ) ≤ Real.log (663 : ℕ) / 2 := by
    have h := (log_br_663).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (663 : ℕ) / 2 ≤ ((259871/80000 : ℚ) : ℝ) := by
    have h := (log_br_663).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6447913/10000000) (δ := 142821/5000000000) 1142 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_664 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (664 : ℕ) / 2)) - ((-2389679/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64982821/20000000 : ℚ) : ℝ) ≤ Real.log (664 : ℕ) / 2 := by
    have h := (log_br_664).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (664 : ℕ) / 2 ≤ ((32491411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_664).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35542611/50000000) (δ := 285633/10000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_665 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (665 : ℕ) / 2)) - ((-4016471/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6499787/2000000 : ℚ) : ℝ) ≤ Real.log (665 : ℕ) / 2 := by
    have h := (log_br_665).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (665 : ℕ) / 2 ≤ ((64997871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_665).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1984111/4000000) (δ := 28557/1000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_666 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (666 : ℕ) / 2)) - ((4301599/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2031653/625000 : ℚ) : ℝ) ≤ Real.log (666 : ℕ) / 2 := by
    have h := (log_br_666).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (666 : ℕ) / 2 ≤ ((65012897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_666).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -703829/2500000) (δ := 28557/1000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_667 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (667 : ℕ) / 2)) - ((9639313/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((650279/200000 : ℚ) : ℝ) ≤ Real.log (667 : ℕ) / 2 := by
    have h := (log_br_667).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (667 : ℕ) / 2 ≤ ((65027901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_667).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -134699/2000000) (δ := 28557/1000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_668 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (668 : ℕ) / 2)) - ((16663/20000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65042881/20000000 : ℚ) : ℝ) ≤ Real.log (668 : ℕ) / 2 := by
    have h := (log_br_668).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (668 : ℕ) / 2 ≤ ((32521441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_668).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3662607/25000000) (δ := 285633/10000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_669 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (669 : ℕ) / 2)) - ((325623/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((813223/250000 : ℚ) : ℝ) ≤ Real.log (669 : ℕ) / 2 := by
    have h := (log_br_669).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (669 : ℕ) / 2 ≤ ((65057841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_669).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 90011/250000) (δ := 28557/1000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_670 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (670 : ℕ) / 2)) - ((-6610989/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8134097/2500000 : ℚ) : ℝ) ≤ Real.log (670 : ℕ) / 2 := by
    have h := (log_br_670).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (670 : ℕ) / 2 ≤ ((65072779/20000000 : ℚ) : ℝ) := by
    have h := (log_br_670).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7165871/12500000) (δ := 856633/10000000000) 1142 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_671 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (671 : ℕ) / 2)) - ((-9999953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65087691/20000000 : ℚ) : ℝ) ≤ Real.log (671 : ℕ) / 2 := by
    have h := (log_br_671).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (671 : ℕ) / 2 ≤ ((16271923/5000000 : ℚ) : ℝ) := by
    have h := (log_br_671).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7846293/10000000) (δ := 57101/2000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_672 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (672 : ℕ) / 2)) - ((-1314837/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65102583/20000000 : ℚ) : ℝ) ≤ Real.log (672 : ℕ) / 2 := by
    have h := (log_br_672).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (672 : ℕ) / 2 ≤ ((8137823/2500000 : ℚ) : ℝ) := by
    have h := (log_br_672).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -286023/500000) (δ := 57101/2000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_673 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (673 : ℕ) / 2)) - ((131309/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65117453/20000000 : ℚ) : ℝ) ≤ Real.log (673 : ℕ) / 2 := by
    have h := (log_br_673).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (673 : ℕ) / 2 ≤ ((32558727/10000000 : ℚ) : ℝ) := by
    have h := (log_br_673).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1439107/4000000) (δ := 57101/2000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_674 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (674 : ℕ) / 2)) - ((2075561/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((651323/200000 : ℚ) : ℝ) ≤ Real.log (674 : ℕ) / 2 := by
    have h := (log_br_674).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (674 : ℕ) / 2 ≤ ((65132303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_674).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2956431/20000000) (δ := 171301/2000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_675 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (675 : ℕ) / 2)) - ((387043/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32573563/10000000 : ℚ) : ℝ) ≤ Real.log (675 : ℕ) / 2 := by
    have h := (log_br_675).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (675 : ℕ) / 2 ≤ ((65147127/20000000 : ℚ) : ℝ) := by
    have h := (log_br_675).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1595133/25000000) (δ := 142849/5000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_676 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (676 : ℕ) / 2)) - ((113281/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/2000000 : ℚ) : ℝ) ≤ Real.log (676 : ℕ) / 2 := by
    have h := (log_br_676).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (676 : ℕ) / 2 ≤ ((65161931/20000000 : ℚ) : ℝ) := by
    have h := (log_br_676).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13756621/50000000) (δ := 142849/5000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_677 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (677 : ℕ) / 2)) - ((-1825711/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8147089/2500000 : ℚ) : ℝ) ≤ Real.log (677 : ℕ) / 2 := by
    have h := (log_br_677).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (677 : ℕ) / 2 ≤ ((65176713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_677).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48614547/100000000) (δ := 142849/5000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_678 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (678 : ℕ) / 2)) - ((-9379191/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4074467/1250000 : ℚ) : ℝ) ≤ Real.log (678 : ℕ) / 2 := by
    have h := (log_br_678).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (678 : ℕ) / 2 ≤ ((65191473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_678).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 69684447/100000000) (δ := 142849/5000000000) 1142 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_679 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (679 : ℕ) / 2)) - ((-8835619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65206211/20000000 : ℚ) : ℝ) ≤ Real.log (679 : ℕ) / 2 := by
    have h := (log_br_679).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (679 : ℕ) / 2 ≤ ((16301553/5000000 : ℚ) : ℝ) := by
    have h := (log_br_679).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66355263/100000000) (δ := 285627/10000000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_680 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (680 : ℕ) / 2)) - ((-2407423/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65220927/20000000 : ℚ) : ℝ) ≤ Real.log (680 : ℕ) / 2 := by
    have h := (log_br_680).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (680 : ℕ) / 2 ≤ ((1019077/312500 : ℚ) : ℝ) := by
    have h := (log_br_680).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45348173/100000000) (δ := 285627/10000000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_681 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (681 : ℕ) / 2)) - ((5613457/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32617811/10000000 : ℚ) : ℝ) ≤ Real.log (681 : ℕ) / 2 := by
    have h := (log_br_681).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (681 : ℕ) / 2 ≤ ((104377/32000 : ℚ) : ℝ) := by
    have h := (log_br_681).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24369633/100000000) (δ := 856627/10000000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_682 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (682 : ℕ) / 2)) - ((247659/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8156287/2500000 : ℚ) : ℝ) ≤ Real.log (682 : ℕ) / 2 := by
    have h := (log_br_682).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (682 : ℕ) / 2 ≤ ((65250297/20000000 : ℚ) : ℝ) := by
    have h := (log_br_682).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -136957/4000000) (δ := 35697/1250000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_683 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (683 : ℕ) / 2)) - ((7650533/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16316237/5000000 : ℚ) : ℝ) ≤ Real.log (683 : ℕ) / 2 := by
    have h := (log_br_683).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (683 : ℕ) / 2 ≤ ((65264949/20000000 : ℚ) : ℝ) := by
    have h := (log_br_683).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3498361/20000000) (δ := 35697/1250000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_684 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (684 : ℕ) / 2)) - ((71373/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65279579/20000000 : ℚ) : ℝ) ≤ Real.log (684 : ℕ) / 2 := by
    have h := (log_br_684).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (684 : ℕ) / 2 ≤ ((3263979/1000000 : ℚ) : ℝ) := by
    have h := (log_br_684).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38377557/100000000) (δ := 285627/10000000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_685 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (685 : ℕ) / 2)) - ((-3581481/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16323547/5000000 : ℚ) : ℝ) ≤ Real.log (685 : ℕ) / 2 := by
    have h := (log_br_685).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (685 : ℕ) / 2 ≤ ((65294189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_685).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11846381/20000000) (δ := 35697/1250000000) 1142 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_686 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (686 : ℕ) / 2)) - ((-1247701/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8163597/2500000 : ℚ) : ℝ) ≤ Real.log (686 : ℕ) / 2 := by
    have h := (log_br_686).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (686 : ℕ) / 2 ≤ ((65308777/20000000 : ℚ) : ℝ) := by
    have h := (log_br_686).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38511679/50000000) (δ := 57111/2000000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_687 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (687 : ℕ) / 2)) - ((-392227/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32661671/10000000 : ℚ) : ℝ) ≤ Real.log (687 : ℕ) / 2 := by
    have h := (log_br_687).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (687 : ℕ) / 2 ≤ ((65323343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_687).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56230393/100000000) (δ := 57111/2000000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_688 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (688 : ℕ) / 2)) - ((378927/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2041809/625000 : ℚ) : ℝ) ≤ Real.log (688 : ℕ) / 2 := by
    have h := (log_br_688).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (688 : ℕ) / 2 ≤ ((65337889/20000000 : ℚ) : ℝ) := by
    have h := (log_br_688).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17732989/50000000) (δ := 57111/2000000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_689 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (689 : ℕ) / 2)) - ((1662639/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16338103/5000000 : ℚ) : ℝ) ≤ Real.log (689 : ℕ) / 2 := by
    have h := (log_br_689).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (689 : ℕ) / 2 ≤ ((65352413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_689).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1841621/12500000) (δ := 57111/2000000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_690 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (690 : ℕ) / 2)) - ((9716219/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13073383/4000000 : ℚ) : ℝ) ≤ Real.log (690 : ℕ) / 2 := by
    have h := (log_br_690).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (690 : ℕ) / 2 ≤ ((16341729/5000000 : ℚ) : ℝ) := by
    have h := (log_br_690).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1194013/20000000) (δ := 17853/625000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_691 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (691 : ℕ) / 2)) - ((4838201/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32690699/10000000 : ℚ) : ℝ) ≤ Real.log (691 : ℕ) / 2 := by
    have h := (log_br_691).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (691 : ℕ) / 2 ≤ ((65381399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_691).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26644547/100000000) (δ := 57111/2000000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_692 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (692 : ℕ) / 2)) - ((-394049/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65395859/20000000 : ℚ) : ℝ) ≤ Real.log (692 : ℕ) / 2 := by
    have h := (log_br_692).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (692 : ℕ) / 2 ≤ ((3269793/1000000 : ℚ) : ℝ) := by
    have h := (log_br_692).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 378301/800000) (δ := 17853/625000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_693 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (693 : ℕ) / 2)) - ((-4554031/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32705149/10000000 : ℚ) : ℝ) ≤ Real.log (693 : ℕ) / 2 := by
    have h := (log_br_693).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (693 : ℕ) / 2 ≤ ((65410301/20000000 : ℚ) : ℝ) := by
    have h := (log_br_693).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2716029/4000000) (δ := 107081/1250000000) 1142 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_694 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (694 : ℕ) / 2)) - ((-2304771/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65424719/20000000 : ℚ) : ℝ) ≤ Real.log (694 : ℕ) / 2 := by
    have h := (log_br_694).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (694 : ℕ) / 2 ≤ ((817809/250000 : ℚ) : ℝ) := by
    have h := (log_br_694).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34297179/50000000) (δ := 3569/125000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_695 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (695 : ℕ) / 2)) - ((-1718223/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32719559/10000000 : ℚ) : ℝ) ≤ Real.log (695 : ℕ) / 2 := by
    have h := (log_br_695).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (695 : ℕ) / 2 ≤ ((65439119/20000000 : ℚ) : ℝ) := by
    have h := (log_br_695).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24019893/50000000) (δ := 285683/10000000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_696 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (696 : ℕ) / 2)) - ((906109/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8181687/2500000 : ℚ) : ℝ) ≤ Real.log (696 : ℕ) / 2 := by
    have h := (log_br_696).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (696 : ℕ) / 2 ≤ ((65453497/20000000 : ℚ) : ℝ) := by
    have h := (log_br_696).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27515191/100000000) (δ := 285683/10000000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_697 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (697 : ℕ) / 2)) - ((1921687/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32733927/10000000 : ℚ) : ℝ) ≤ Real.log (697 : ℕ) / 2 := by
    have h := (log_br_697).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (697 : ℕ) / 2 ≤ ((13093571/4000000 : ℚ) : ℝ) := by
    have h := (log_br_697).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3509573/50000000) (δ := 285683/10000000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_698 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (698 : ℕ) / 2)) - ((8587983/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6548219/2000000 : ℚ) : ℝ) ≤ Real.log (698 : ℕ) / 2 := by
    have h := (log_br_698).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (698 : ℕ) / 2 ≤ ((65482193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_698).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6723461/50000000) (δ := 21413/250000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_699 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (699 : ℕ) / 2)) - ((2138123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65496507/20000000 : ℚ) : ℝ) ≤ Real.log (699 : ℕ) / 2 := by
    have h := (log_br_699).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (699 : ℕ) / 2 ≤ ((16374127/5000000 : ℚ) : ℝ) := by
    have h := (log_br_699).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8470753/25000000) (δ := 3569/125000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_700 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (700 : ℕ) / 2)) - ((-2826619/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65510803/20000000 : ℚ) : ℝ) ≤ Real.log (700 : ℕ) / 2 := by
    have h := (log_br_700).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (700 : ℕ) / 2 ≤ ((16377701/5000000 : ℚ) : ℝ) := by
    have h := (log_br_700).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6786319/12500000) (δ := 3569/125000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_701 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (701 : ℕ) / 2)) - ((-9880319/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32762539/10000000 : ℚ) : ℝ) ≤ Real.log (701 : ℕ) / 2 := by
    have h := (log_br_701).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (701 : ℕ) / 2 ≤ ((65525079/20000000 : ℚ) : ℝ) := by
    have h := (log_br_701).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37334057/50000000) (δ := 285683/10000000000) 1142 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_702 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (702 : ℕ) / 2)) - ((-3952567/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65539333/20000000 : ℚ) : ℝ) ≤ Real.log (702 : ℕ) / 2 := by
    have h := (log_br_702).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (702 : ℕ) / 2 ≤ ((8192417/2500000 : ℚ) : ℝ) := by
    have h := (log_br_702).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31030539/50000000) (δ := 53537/625000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_703 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (703 : ℕ) / 2)) - ((-987243/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2048549/625000 : ℚ) : ℝ) ≤ Real.log (703 : ℕ) / 2 := by
    have h := (log_br_703).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (703 : ℕ) / 2 ≤ ((65553569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_703).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41742043/100000000) (δ := 35699/1250000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_704 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (704 : ℕ) / 2)) - ((6539479/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65567783/20000000 : ℚ) : ℝ) ≤ Real.log (704 : ℕ) / 2 := by
    have h := (log_br_704).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (704 : ℕ) / 2 ≤ ((8195973/2500000 : ℚ) : ℝ) := by
    have h := (log_br_704).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21450131/100000000) (δ := 285611/10000000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_705 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (705 : ℕ) / 2)) - ((1997747/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65581977/20000000 : ℚ) : ℝ) ≤ Real.log (705 : ℕ) / 2 := by
    have h := (log_br_705).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (705 : ℕ) / 2 ≤ ((3279099/1000000 : ℚ) : ℝ) := by
    have h := (log_br_705).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74173/6250000) (δ := 53537/625000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_706 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (706 : ℕ) / 2)) - ((7235501/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8199519/2500000 : ℚ) : ℝ) ≤ Real.log (706 : ℕ) / 2 := by
    have h := (log_br_706).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (706 : ℕ) / 2 ≤ ((65596153/20000000 : ℚ) : ℝ) := by
    have h := (log_br_706).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19046617/100000000) (δ := 35699/1250000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_707 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (707 : ℕ) / 2)) - ((3691/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32805153/10000000 : ℚ) : ℝ) ≤ Real.log (707 : ℕ) / 2 := by
    have h := (log_br_707).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (707 : ℕ) / 2 ≤ ((65610307/20000000 : ℚ) : ℝ) := by
    have h := (log_br_707).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9812863/25000000) (δ := 35699/1250000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_708 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (708 : ℕ) / 2)) - ((-3608701/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1640611/500000 : ℚ) : ℝ) ≤ Real.log (708 : ℕ) / 2 := by
    have h := (log_br_708).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (708 : ℕ) / 2 ≤ ((65624441/20000000 : ℚ) : ℝ) := by
    have h := (log_br_708).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59427737/100000000) (δ := 35699/1250000000) 1142 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_709 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (709 : ℕ) / 2)) - ((-9991397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13127711/4000000 : ℚ) : ℝ) ≤ Real.log (709 : ℕ) / 2 := by
    have h := (log_br_709).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (709 : ℕ) / 2 ≤ ((16409639/5000000 : ℚ) : ℝ) := by
    have h := (log_br_709).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77502733/100000000) (δ := 8927/312500000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_710 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (710 : ℕ) / 2)) - ((-6627953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65652649/20000000 : ℚ) : ℝ) ≤ Real.log (710 : ℕ) / 2 := by
    have h := (log_br_710).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (710 : ℕ) / 2 ≤ ((1313053/400000 : ℚ) : ℝ) := by
    have h := (log_br_710).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14345887/25000000) (δ := 8927/312500000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_711 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (711 : ℕ) / 2)) - ((790543/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16416681/5000000 : ℚ) : ℝ) ≤ Real.log (711 : ℕ) / 2 := by
    have h := (log_br_711).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (711 : ℕ) / 2 ≤ ((2626669/800000 : ℚ) : ℝ) := by
    have h := (log_br_711).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18645743/50000000) (δ := 285539/10000000000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_712 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (712 : ℕ) / 2)) - ((3859033/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65680779/20000000 : ℚ) : ℝ) ≤ Real.log (712 : ℕ) / 2 := by
    have h := (log_br_712).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (712 : ℕ) / 2 ≤ ((3284039/1000000 : ℚ) : ℝ) := by
    have h := (log_br_712).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17227973/100000000) (δ := 8927/312500000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_713 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (713 : ℕ) / 2)) - ((9937033/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32847407/10000000 : ℚ) : ℝ) ≤ Real.log (713 : ℕ) / 2 := by
    have h := (log_br_713).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (713 : ℕ) / 2 ≤ ((13138963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_713).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2806989/100000000) (δ := 285539/10000000000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_714 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (714 : ℕ) / 2)) - ((1223483/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65708829/20000000 : ℚ) : ℝ) ≤ Real.log (714 : ℕ) / 2 := by
    have h := (log_br_714).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (714 : ℕ) / 2 ≤ ((6570883/2000000 : ℚ) : ℝ) := by
    have h := (log_br_714).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11406701/50000000) (δ := 8927/312500000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_715 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (715 : ℕ) / 2)) - ((-280891/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2628913/800000 : ℚ) : ℝ) ≤ Real.log (715 : ℕ) / 2 := by
    have h := (log_br_715).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (715 : ℕ) / 2 ≤ ((32861413/10000000 : ℚ) : ℝ) := by
    have h := (log_br_715).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10698173/25000000) (δ := 8927/312500000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_716 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (716 : ℕ) / 2)) - ((-806933/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65736801/20000000 : ℚ) : ℝ) ≤ Real.log (716 : ℕ) / 2 := by
    have h := (log_br_716).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (716 : ℕ) / 2 ≤ ((32868401/10000000 : ℚ) : ℝ) := by
    have h := (log_br_716).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7842929/12500000) (δ := 8927/312500000) 1142 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_717 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (717 : ℕ) / 2)) - ((-9864037/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32875379/10000000 : ℚ) : ℝ) ≤ Real.log (717 : ℕ) / 2 := by
    have h := (log_br_717).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (717 : ℕ) / 2 ≤ ((65750759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_717).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9301573/12500000) (δ := 71417/2500000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_718 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (718 : ℕ) / 2)) - ((-572789/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13152939/4000000 : ℚ) : ℝ) ≤ Real.log (718 : ℕ) / 2 := by
    have h := (log_br_718).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (718 : ℕ) / 2 ≤ ((8220587/2500000 : ℚ) : ℝ) := by
    have h := (log_br_718).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13629379/25000000) (δ := 57107/2000000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_719 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (719 : ℕ) / 2)) - ((28713/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65778613/20000000 : ℚ) : ℝ) ≤ Real.log (719 : ℕ) / 2 := by
    have h := (log_br_719).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (719 : ℕ) / 2 ≤ ((32889307/10000000 : ℚ) : ℝ) := by
    have h := (log_br_719).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34649571/100000000) (δ := 57107/2000000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_720 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (720 : ℕ) / 2)) - ((829631/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((257002/78125 : ℚ) : ℝ) ≤ Real.log (720 : ℕ) / 2 := by
    have h := (log_br_720).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (720 : ℕ) / 2 ≤ ((65792513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_720).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14808749/100000000) (δ := 71417/2500000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_721 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (721 : ℕ) / 2)) - ((4900193/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65806391/20000000 : ℚ) : ℝ) ≤ Real.log (721 : ℕ) / 2 := by
    have h := (log_br_721).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (721 : ℕ) / 2 ≤ ((8225799/2500000 : ℚ) : ℝ) := by
    have h := (log_br_721).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1250881/25000000) (δ := 57107/2000000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_722 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (722 : ℕ) / 2)) - ((5473959/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65820251/20000000 : ℚ) : ℝ) ≤ Real.log (722 : ℕ) / 2 := by
    have h := (log_br_722).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (722 : ℕ) / 2 ≤ ((16455063/5000000 : ℚ) : ℝ) := by
    have h := (log_br_722).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12394337/50000000) (δ := 57107/2000000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_723 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (723 : ℕ) / 2)) - ((-2095079/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16458523/5000000 : ℚ) : ℝ) ≤ Real.log (723 : ℕ) / 2 := by
    have h := (log_br_723).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (723 : ℕ) / 2 ≤ ((65834093/20000000 : ℚ) : ℝ) := by
    have h := (log_br_723).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44546701/100000000) (δ := 71417/2500000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_724 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (724 : ℕ) / 2)) - ((-1683213/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65847913/20000000 : ℚ) : ℝ) ≤ Real.log (724 : ℕ) / 2 := by
    have h := (log_br_724).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (724 : ℕ) / 2 ≤ ((32923957/10000000 : ℚ) : ℝ) := by
    have h := (log_br_724).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64276179/100000000) (δ := 57107/2000000000) 1142 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_725 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (725 : ℕ) / 2)) - ((-9764171/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16465429/5000000 : ℚ) : ℝ) ≤ Real.log (725 : ℕ) / 2 := by
    have h := (log_br_725).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (725 : ℕ) / 2 ≤ ((65861717/20000000 : ℚ) : ℝ) := by
    have h := (log_br_725).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73099671/100000000) (δ := 285607/10000000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_726 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (726 : ℕ) / 2)) - ((-5363649/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((131751/40000 : ℚ) : ℝ) ≤ Real.log (726 : ℕ) / 2 := by
    have h := (log_br_726).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (726 : ℕ) / 2 ≤ ((65875501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_726).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53423011/100000000) (δ := 285607/10000000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_727 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (727 : ℕ) / 2)) - ((2180347/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4118079/1250000 : ℚ) : ℝ) ≤ Real.log (727 : ℕ) / 2 := by
    have h := (log_br_727).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (727 : ℕ) / 2 ≤ ((13177853/4000000 : ℚ) : ℝ) := by
    have h := (log_br_727).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33774901/100000000) (δ := 285607/10000000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_728 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (728 : ℕ) / 2)) - ((4219997/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6590301/2000000 : ℚ) : ℝ) ≤ Real.log (728 : ℕ) / 2 := by
    have h := (log_br_728).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (728 : ℕ) / 2 ≤ ((65903011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_728).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7076243/50000000) (δ := 285607/10000000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_729 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (729 : ℕ) / 2)) - ((4881971/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65916737/20000000 : ℚ) : ℝ) ≤ Real.log (729 : ℕ) / 2 := by
    have h := (log_br_729).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (729 : ℕ) / 2 ≤ ((32958369/10000000 : ℚ) : ℝ) := by
    have h := (log_br_729).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2721403/50000000) (δ := 71399/2500000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_730 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (730 : ℕ) / 2)) - ((168729/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13186089/4000000 : ℚ) : ℝ) ≤ Real.log (730 : ℕ) / 2 := by
    have h := (log_br_730).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (730 : ℕ) / 2 ≤ ((32965223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_730).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 781593/3125000) (δ := 71399/2500000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_731 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (731 : ℕ) / 2)) - ((-2097161/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32972067/10000000 : ℚ) : ℝ) ≤ Real.log (731 : ℕ) / 2 := by
    have h := (log_br_731).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (731 : ℕ) / 2 ≤ ((13188827/4000000 : ℚ) : ℝ) := by
    have h := (log_br_731).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5569003/12500000) (δ := 285607/10000000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_732 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (732 : ℕ) / 2)) - ((-8370663/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13191561/4000000 : ℚ) : ℝ) ≤ Real.log (732 : ℕ) / 2 := by
    have h := (log_br_732).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (732 : ℕ) / 2 ≤ ((32978903/10000000 : ℚ) : ℝ) := by
    have h := (log_br_732).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4004211/6250000) (δ := 71399/2500000000) 1142 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_733 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (733 : ℕ) / 2)) - ((-9799409/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((257701/78125 : ℚ) : ℝ) ≤ Real.log (733 : ℕ) / 2 := by
    have h := (log_br_733).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (733 : ℕ) / 2 ≤ ((65971459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_733).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36762013/50000000) (δ := 856679/10000000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_734 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (734 : ℕ) / 2)) - ((-2788949/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6598509/2000000 : ℚ) : ℝ) ≤ Real.log (734 : ℕ) / 2 := by
    have h := (log_br_734).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (734 : ℕ) / 2 ≤ ((65985091/20000000 : ℚ) : ℝ) := by
    have h := (log_br_734).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54062919/100000000) (δ := 71381/2500000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_735 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (735 : ℕ) / 2)) - ((922873/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4124919/1250000 : ℚ) : ℝ) ≤ Real.log (735 : ℕ) / 2 := by
    have h := (log_br_735).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (735 : ℕ) / 2 ≤ ((13199741/4000000 : ℚ) : ℝ) := by
    have h := (log_br_735).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17314467/50000000) (δ := 71381/2500000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_736 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (736 : ℕ) / 2)) - ((1025441/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66012301/20000000 : ℚ) : ℝ) ≤ Real.log (736 : ℕ) / 2 := by
    have h := (log_br_736).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (736 : ℕ) / 2 ≤ ((33006151/10000000 : ℚ) : ℝ) := by
    have h := (log_br_736).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -951201/6250000) (δ := 285679/10000000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_737 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (737 : ℕ) / 2)) - ((1972349/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33012939/10000000 : ℚ) : ℝ) ≤ Real.log (737 : ℕ) / 2 := by
    have h := (log_br_737).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (737 : ℕ) / 2 ≤ ((66025879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_737).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4161951/100000000) (δ := 71381/2500000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_738 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (738 : ℕ) / 2)) - ((5891789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33019719/10000000 : ℚ) : ℝ) ≤ Real.log (738 : ℕ) / 2 := by
    have h := (log_br_738).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (738 : ℕ) / 2 ≤ ((66039439/20000000 : ℚ) : ℝ) := by
    have h := (log_br_738).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23518851/100000000) (δ := 71381/2500000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_739 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (739 : ℕ) / 2)) - ((-356651/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66052979/20000000 : ℚ) : ℝ) ≤ Real.log (739 : ℕ) / 2 := by
    have h := (log_br_739).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (739 : ℕ) / 2 ≤ ((3302649/1000000 : ℚ) : ℝ) := by
    have h := (log_br_739).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42848629/100000000) (δ := 285679/10000000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_740 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (740 : ℕ) / 2)) - ((-7927181/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66066501/20000000 : ℚ) : ℝ) ≤ Real.log (740 : ℕ) / 2 := by
    have h := (log_br_740).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (740 : ℕ) / 2 ≤ ((33033251/10000000 : ℚ) : ℝ) := by
    have h := (log_br_740).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15537821/25000000) (δ := 285679/10000000000) 1142 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_741 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (741 : ℕ) / 2)) - ((-620829/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33040003/10000000 : ℚ) : ℝ) ≤ Real.log (741 : ℕ) / 2 := by
    have h := (log_br_741).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (741 : ℕ) / 2 ≤ ((66080007/20000000 : ℚ) : ℝ) := by
    have h := (log_br_741).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37824981/50000000) (δ := 71413/2500000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_742 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (742 : ℕ) / 2)) - ((-197747/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16523373/5000000 : ℚ) : ℝ) ≤ Real.log (742 : ℕ) / 2 := by
    have h := (log_br_742).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (742 : ℕ) / 2 ≤ ((66093493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_742).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56398697/100000000) (δ := 71413/2500000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_743 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (743 : ℕ) / 2)) - ((83773/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((826337/250000 : ℚ) : ℝ) ≤ Real.log (743 : ℕ) / 2 := by
    have h := (log_br_743).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (743 : ℕ) / 2 ≤ ((66106961/20000000 : ℚ) : ℝ) := by
    have h := (log_br_743).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37173127/100000000) (δ := 71413/2500000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_744 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (744 : ℕ) / 2)) - ((1881277/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6612041/2000000 : ℚ) : ℝ) ≤ Real.log (744 : ℕ) / 2 := by
    have h := (log_br_744).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (744 : ℕ) / 2 ≤ ((66120411/20000000 : ℚ) : ℝ) := by
    have h := (log_br_744).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4493313/25000000) (δ := 71413/2500000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_745 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (745 : ℕ) / 2)) - ((624279/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33066921/10000000 : ℚ) : ℝ) ≤ Real.log (745 : ℕ) / 2 := by
    have h := (log_br_745).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (745 : ℕ) / 2 ≤ ((66133843/20000000 : ℚ) : ℝ) := by
    have h := (log_br_745).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37529/3125000) (δ := 71413/2500000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_746 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (746 : ℕ) / 2)) - ((429133/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13229451/4000000 : ℚ) : ℝ) ≤ Real.log (746 : ℕ) / 2 := by
    have h := (log_br_746).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (746 : ℕ) / 2 ≤ ((33073629/10000000 : ℚ) : ℝ) := by
    have h := (log_br_746).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20349413/100000000) (δ := 214163/2500000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_747 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (747 : ℕ) / 2)) - ((-40173/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66160651/20000000 : ℚ) : ℝ) ≤ Real.log (747 : ℕ) / 2 := by
    have h := (log_br_747).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (747 : ℕ) / 2 ≤ ((16540163/5000000 : ℚ) : ℝ) := by
    have h := (log_br_747).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4933847/12500000) (δ := 285551/10000000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_748 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (748 : ℕ) / 2)) - ((-6975113/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66174029/20000000 : ℚ) : ℝ) ≤ Real.log (748 : ℕ) / 2 := by
    have h := (log_br_748).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (748 : ℕ) / 2 ≤ ((6617403/2000000 : ℚ) : ℝ) := by
    have h := (log_br_748).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58567871/100000000) (δ := 285551/10000000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_749 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (749 : ℕ) / 2)) - ((-9993513/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66187389/20000000 : ℚ) : ℝ) ≤ Real.log (749 : ℕ) / 2 := by
    have h := (log_br_749).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (749 : ℕ) / 2 ≤ ((6618739/2000000 : ℚ) : ℝ) := by
    have h := (log_br_749).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77639271/100000000) (δ := 285551/10000000000) 1142 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_750 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (750 : ℕ) / 2)) - ((-1495853/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16550183/5000000 : ℚ) : ℝ) ≤ Real.log (750 : ℕ) / 2 := by
    have h := (log_br_750).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (750 : ℕ) / 2 ≤ ((66200733/20000000 : ℚ) : ℝ) := by
    have h := (log_br_750).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60393229/100000000) (δ := 285623/10000000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_751 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (751 : ℕ) / 2)) - ((-210083/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8276757/2500000 : ℚ) : ℝ) ≤ Real.log (751 : ℕ) / 2 := by
    have h := (log_br_751).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (751 : ℕ) / 2 ≤ ((66214057/20000000 : ℚ) : ℝ) := by
    have h := (log_br_751).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41373219/100000000) (δ := 285623/10000000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_752 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (752 : ℕ) / 2)) - ((1250883/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66227363/20000000 : ℚ) : ℝ) ≤ Real.log (752 : ℕ) / 2 := by
    have h := (log_br_752).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (752 : ℕ) / 2 ≤ ((16556841/5000000 : ℚ) : ℝ) := by
    have h := (log_br_752).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22377477/100000000) (δ := 14279/500000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_753 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (753 : ℕ) / 2)) - ((9907259/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16560163/5000000 : ℚ) : ℝ) ≤ Real.log (753 : ℕ) / 2 := by
    have h := (log_br_753).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (753 : ℕ) / 2 ≤ ((66240653/20000000 : ℚ) : ℝ) := by
    have h := (log_br_753).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3407429/100000000) (δ := 285623/10000000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_754 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (754 : ℕ) / 2)) - ((4065097/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66253923/20000000 : ℚ) : ℝ) ≤ Real.log (754 : ℕ) / 2 := by
    have h := (log_br_754).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (754 : ℕ) / 2 ≤ ((16563481/5000000 : ℚ) : ℝ) := by
    have h := (log_br_754).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15536923/100000000) (δ := 14279/500000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_755 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (755 : ℕ) / 2)) - ((191329/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66267177/20000000 : ℚ) : ℝ) ≤ Real.log (755 : ℕ) / 2 := by
    have h := (log_br_755).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (755 : ℕ) / 2 ≤ ((33133589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_755).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2153563/6250000) (δ := 14279/500000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_756 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (756 : ℕ) / 2)) - ((-5339451/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66280413/20000000 : ℚ) : ℝ) ≤ Real.log (756 : ℕ) / 2 := by
    have h := (log_br_756).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (756 : ℕ) / 2 ≤ ((33140207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_756).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26675699/50000000) (δ := 14279/500000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_757 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (757 : ℕ) / 2)) - ((-9682329/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((517919/156250 : ℚ) : ℝ) ≤ Real.log (757 : ℕ) / 2 := by
    have h := (log_br_757).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (757 : ℕ) / 2 ≤ ((66293633/20000000 : ℚ) : ℝ) := by
    have h := (log_br_757).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 72221521/100000000) (δ := 285623/10000000000) 1142 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_758 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (758 : ℕ) / 2)) - ((-8770809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66306833/20000000 : ℚ) : ℝ) ≤ Real.log (758 : ℕ) / 2 := by
    have h := (log_br_758).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (758 : ℕ) / 2 ≤ ((33153417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_758).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16503421/25000000) (δ := 142847/5000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_759 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (759 : ℕ) / 2)) - ((-389581/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66320017/20000000 : ℚ) : ℝ) ≤ Real.log (759 : ℕ) / 2 := by
    have h := (log_br_759).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (759 : ℕ) / 2 ≤ ((33160009/10000000 : ℚ) : ℝ) := by
    have h := (log_br_759).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11798381/25000000) (δ := 142847/5000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_760 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (760 : ℕ) / 2)) - ((1053279/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((259114/78125 : ℚ) : ℝ) ≤ Real.log (760 : ℕ) / 2 := by
    have h := (log_br_760).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (760 : ℕ) / 2 ≤ ((13266637/4000000 : ℚ) : ℝ) := by
    have h := (log_br_760).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -443713/1562500) (δ := 285509/10000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_761 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (761 : ℕ) / 2)) - ((9267619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66346333/20000000 : ℚ) : ℝ) ≤ Real.log (761 : ℕ) / 2 := by
    have h := (log_br_761).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (761 : ℕ) / 2 ≤ ((33173167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_761).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4813717/50000000) (δ := 142847/5000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_762 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (762 : ℕ) / 2)) - ((4671083/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13271893/4000000 : ℚ) : ℝ) ≤ Real.log (762 : ℕ) / 2 := by
    have h := (log_br_762).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (762 : ℕ) / 2 ≤ ((33179733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_762).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 284953/3125000) (δ := 142847/5000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_763 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (763 : ℕ) / 2)) - ((882857/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3318629/1000000 : ℚ) : ℝ) ≤ Real.log (763 : ℕ) / 2 := by
    have h := (log_br_763).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (763 : ℕ) / 2 ≤ ((66372581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_763).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13920079/50000000) (δ := 285509/10000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_764 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (764 : ℕ) / 2)) - ((-1432869/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66385677/20000000 : ℚ) : ℝ) ≤ Real.log (764 : ℕ) / 2 := by
    have h := (log_br_764).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (764 : ℕ) / 2 ≤ ((33192839/10000000 : ℚ) : ℝ) := by
    have h := (log_br_764).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23268063/50000000) (δ := 142847/5000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_765 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (765 : ℕ) / 2)) - ((-1722347/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33199379/10000000 : ℚ) : ℝ) ≤ Real.log (765 : ℕ) / 2 := by
    have h := (log_br_765).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (765 : ℕ) / 2 ≤ ((66398759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_765).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65209253/100000000) (δ := 285509/10000000000) 1142 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_766 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (766 : ℕ) / 2)) - ((-4887349/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66411821/20000000 : ℚ) : ℝ) ≤ Real.log (766 : ℕ) / 2 := by
    have h := (log_br_766).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (766 : ℕ) / 2 ≤ ((33205911/10000000 : ℚ) : ℝ) := by
    have h := (log_br_766).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73222947/100000000) (δ := 142783/5000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_767 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (767 : ℕ) / 2)) - ((-2877183/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16606217/5000000 : ℚ) : ℝ) ≤ Real.log (767 : ℕ) / 2 := by
    have h := (log_br_767).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (767 : ℕ) / 2 ≤ ((66424869/20000000 : ℚ) : ℝ) := by
    have h := (log_br_767).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10919671/20000000) (δ := 285637/10000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_768 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (768 : ℕ) / 2)) - ((326113/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66437897/20000000 : ℚ) : ℝ) ≤ Real.log (768 : ℕ) / 2 := by
    have h := (log_br_768).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (768 : ℕ) / 2 ≤ ((33218949/10000000 : ℚ) : ℝ) := by
    have h := (log_br_768).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35999457/100000000) (δ := 142783/5000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_769 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (769 : ℕ) / 2)) - ((3833879/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66450909/20000000 : ℚ) : ℝ) ≤ Real.log (769 : ℕ) / 2 := by
    have h := (log_br_769).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (769 : ℕ) / 2 ≤ ((6645091/2000000 : ℚ) : ℝ) := by
    have h := (log_br_769).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17424827/100000000) (δ := 142783/5000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_770 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (770 : ℕ) / 2)) - ((9989841/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13292781/4000000 : ℚ) : ℝ) ≤ Real.log (770 : ℕ) / 2 := by
    have h := (log_br_770).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (770 : ℕ) / 2 ≤ ((33231953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_770).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1126963/100000000) (δ := 142783/5000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_771 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (771 : ℕ) / 2)) - ((1413189/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66476883/20000000 : ℚ) : ℝ) ≤ Real.log (771 : ℕ) / 2 := by
    have h := (log_br_771).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (771 : ℕ) / 2 ≤ ((16619221/5000000 : ℚ) : ℝ) := by
    have h := (log_br_771).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9826529/50000000) (δ := 142783/5000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_772 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (772 : ℕ) / 2)) - ((445291/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13297969/4000000 : ℚ) : ℝ) ≤ Real.log (772 : ℕ) / 2 := by
    have h := (log_br_772).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (772 : ℕ) / 2 ≤ ((33244923/10000000 : ℚ) : ℝ) := by
    have h := (log_br_772).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38156313/100000000) (δ := 142783/5000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_773 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (773 : ℕ) / 2)) - ((-3200451/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6650279/2000000 : ℚ) : ℝ) ≤ Real.log (773 : ℕ) / 2 := by
    have h := (log_br_773).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (773 : ℕ) / 2 ≤ ((66502791/20000000 : ℚ) : ℝ) := by
    have h := (log_br_773).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 566353/1000000) (δ := 285637/10000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_774 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (774 : ℕ) / 2)) - ((-4952471/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33257859/10000000 : ℚ) : ℝ) ≤ Real.log (774 : ℕ) / 2 := by
    have h := (log_br_774).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (774 : ℕ) / 2 ≤ ((66515719/20000000 : ℚ) : ℝ) := by
    have h := (log_br_774).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3754501/5000000) (δ := 285637/10000000000) 1142 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_775 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (775 : ℕ) / 2)) - ((-41287/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6652863/2000000 : ℚ) : ℝ) ≤ Real.log (775 : ℕ) / 2 := by
    have h := (log_br_775).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (775 : ℕ) / 2 ≤ ((66528631/20000000 : ℚ) : ℝ) := by
    have h := (log_br_775).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15889433/25000000) (δ := 142819/5000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_776 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (776 : ℕ) / 2)) - ((-2330457/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2661661/800000 : ℚ) : ℝ) ≤ Real.log (776 : ℕ) / 2 := by
    have h := (log_br_776).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (776 : ℕ) / 2 ≤ ((33270763/10000000 : ℚ) : ℝ) := by
    have h := (log_br_776).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1128753/2500000) (δ := 57113/2000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_777 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (777 : ℕ) / 2)) - ((959071/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66554403/20000000 : ℚ) : ℝ) ≤ Real.log (777 : ℕ) / 2 := by
    have h := (log_br_777).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (777 : ℕ) / 2 ≤ ((16638601/5000000 : ℚ) : ℝ) := by
    have h := (log_br_777).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1070671/4000000) (δ := 57113/2000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_778 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (778 : ℕ) / 2)) - ((9439983/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13313453/4000000 : ℚ) : ℝ) ≤ Real.log (778 : ℕ) / 2 := by
    have h := (log_br_778).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (778 : ℕ) / 2 ≤ ((33283633/10000000 : ℚ) : ℝ) := by
    have h := (log_br_778).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -840627/10000000) (δ := 57113/2000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_779 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (779 : ℕ) / 2)) - ((4610741/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6658011/2000000 : ℚ) : ℝ) ≤ Real.log (779 : ℕ) / 2 := by
    have h := (log_br_779).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (779 : ℕ) / 2 ≤ ((66580111/20000000 : ℚ) : ℝ) := by
    have h := (log_br_779).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 620623/6250000) (δ := 142819/5000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_780 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (780 : ℕ) / 2)) - ((2134499/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66592939/20000000 : ℚ) : ℝ) ≤ Real.log (780 : ℕ) / 2 := by
    have h := (log_br_780).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (780 : ℕ) / 2 ≤ ((3329647/1000000 : ℚ) : ℝ) := by
    have h := (log_br_780).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5648673/20000000) (δ := 57113/2000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_781 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (781 : ℕ) / 2)) - ((-1432173/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66605751/20000000 : ℚ) : ℝ) ≤ Real.log (781 : ℕ) / 2 := by
    have h := (log_br_781).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (781 : ℕ) / 2 ≤ ((8325719/2500000 : ℚ) : ℝ) := by
    have h := (log_br_781).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9306499/20000000) (δ := 57113/2000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_782 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (782 : ℕ) / 2)) - ((-106589/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66618547/20000000 : ℚ) : ℝ) ≤ Real.log (782 : ℕ) / 2 := by
    have h := (log_br_782).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (782 : ℕ) / 2 ≤ ((16654637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_782).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12959757/20000000) (δ := 57113/2000000000) 1142 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_783 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (783 : ℕ) / 2)) - ((-4919183/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33315663/10000000 : ℚ) : ℝ) ≤ Real.log (783 : ℕ) / 2 := by
    have h := (log_br_783).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (783 : ℕ) / 2 ≤ ((66631327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_783).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2961553/4000000) (δ := 28551/1000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_784 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (784 : ℕ) / 2)) - ((-3073211/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/2000000 : ℚ) : ℝ) ≤ Real.log (784 : ℕ) / 2 := by
    have h := (log_br_784).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (784 : ℕ) / 2 ≤ ((66644091/20000000 : ℚ) : ℝ) := by
    have h := (log_br_784).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11163643/20000000) (δ := 28551/1000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_785 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (785 : ℕ) / 2)) - ((658737/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66656837/20000000 : ℚ) : ℝ) ≤ Real.log (785 : ℕ) / 2 := by
    have h := (log_br_785).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (785 : ℕ) / 2 ≤ ((33328419/10000000 : ℚ) : ℝ) := by
    have h := (log_br_785).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37621873/100000000) (δ := 285693/10000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_786 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (786 : ℕ) / 2)) - ((7123243/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66669567/20000000 : ℚ) : ℝ) ≤ Real.log (786 : ℕ) / 2 := by
    have h := (log_br_786).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (786 : ℕ) / 2 ≤ ((260428/78125 : ℚ) : ℝ) := by
    have h := (log_br_786).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9724899/50000000) (δ := 285693/10000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_787 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (787 : ℕ) / 2)) - ((9986501/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33341141/10000000 : ℚ) : ℝ) ≤ Real.log (787 : ℕ) / 2 := by
    have h := (log_br_787).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (787 : ℕ) / 2 ≤ ((66682283/20000000 : ℚ) : ℝ) := by
    have h := (log_br_787).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -259827/20000000) (δ := 28551/1000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_788 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (788 : ℕ) / 2)) - ((1954747/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3334749/1000000 : ℚ) : ℝ) ≤ Real.log (788 : ℕ) / 2 := by
    have h := (log_br_788).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (788 : ℕ) / 2 ≤ ((66694981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_788).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 841363/5000000) (δ := 28551/1000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_789 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (789 : ℕ) / 2)) - ((863187/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66707663/20000000 : ℚ) : ℝ) ≤ Real.log (789 : ℕ) / 2 := by
    have h := (log_br_789).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (789 : ℕ) / 2 ≤ ((4169229/1250000 : ℚ) : ℝ) := by
    have h := (log_br_789).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17466121/50000000) (δ := 285693/10000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_790 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (790 : ℕ) / 2)) - ((-2612251/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66720329/20000000 : ℚ) : ℝ) ≤ Real.log (790 : ℕ) / 2 := by
    have h := (log_br_790).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (790 : ℕ) / 2 ≤ ((6672033/2000000 : ℚ) : ℝ) := by
    have h := (log_br_790).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53012957/100000000) (δ := 285693/10000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_791 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (791 : ℕ) / 2)) - ((-298657/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66732979/20000000 : ℚ) : ℝ) ≤ Real.log (791 : ℕ) / 2 := by
    have h := (log_br_791).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (791 : ℕ) / 2 ≤ ((3336649/1000000 : ℚ) : ℝ) := by
    have h := (log_br_791).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4441927/6250000) (δ := 285693/10000000000) 1142 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_792 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (792 : ℕ) / 2)) - ((-2280021/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66745613/20000000 : ℚ) : ℝ) ≤ Real.log (792 : ℕ) / 2 := by
    have h := (log_br_792).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (792 : ℕ) / 2 ≤ ((33372807/10000000 : ℚ) : ℝ) := by
    have h := (log_br_792).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13594753/20000000) (δ := 142791/5000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_793 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (793 : ℕ) / 2)) - ((-2073483/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8344779/2500000 : ℚ) : ℝ) ≤ Real.log (793 : ℕ) / 2 := by
    have h := (log_br_793).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (793 : ℕ) / 2 ≤ ((66758233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_793).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49960143/100000000) (δ := 285621/10000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_794 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (794 : ℕ) / 2)) - ((359793/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33385417/10000000 : ℚ) : ℝ) ≤ Real.log (794 : ℕ) / 2 := by
    have h := (log_br_794).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (794 : ℕ) / 2 ≤ ((13354167/4000000 : ℚ) : ℝ) := by
    have h := (log_br_794).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7992697/25000000) (δ := 285621/10000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_795 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (795 : ℕ) / 2)) - ((8471947/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66783421/20000000 : ℚ) : ℝ) ≤ Real.log (795 : ℕ) / 2 := by
    have h := (log_br_795).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (795 : ℕ) / 2 ≤ ((33391711/10000000 : ℚ) : ℝ) := by
    have h := (log_br_795).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2800569/20000000) (δ := 142791/5000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_796 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (796 : ℕ) / 2)) - ((617251/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66795991/20000000 : ℚ) : ℝ) ≤ Real.log (796 : ℕ) / 2 := by
    have h := (log_br_796).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (796 : ℕ) / 2 ≤ ((8349499/2500000 : ℚ) : ℝ) := by
    have h := (log_br_796).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 394083/10000000) (δ := 142791/5000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_797 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (797 : ℕ) / 2)) - ((801703/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33404273/10000000 : ℚ) : ℝ) ≤ Real.log (797 : ℕ) / 2 := by
    have h := (log_br_797).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (797 : ℕ) / 2 ≤ ((66808547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_797).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5465773/25000000) (δ := 285621/10000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_798 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (798 : ℕ) / 2)) - ((-19703/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13364217/4000000 : ℚ) : ℝ) ≤ Real.log (798 : ℕ) / 2 := by
    have h := (log_br_798).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (798 : ℕ) / 2 ≤ ((33410543/10000000 : ℚ) : ℝ) := by
    have h := (log_br_798).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7952503/20000000) (δ := 142791/5000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_799 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (799 : ℕ) / 2)) - ((-6704571/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66833609/20000000 : ℚ) : ℝ) ≤ Real.log (799 : ℕ) / 2 := by
    have h := (log_br_799).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (799 : ℕ) / 2 ≤ ((6683361/2000000 : ℚ) : ℝ) := by
    have h := (log_br_799).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2305621/4000000) (δ := 142791/5000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_800 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (800 : ℕ) / 2)) - ((-4962979/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66846117/20000000 : ℚ) : ℝ) ≤ Real.log (800 : ℕ) / 2 := by
    have h := (log_br_800).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (800 : ℕ) / 2 ≤ ((33423059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_800).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15099139/20000000) (δ := 142791/5000000000) 1142 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_801 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (801 : ℕ) / 2)) - ((-4150447/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66858609/20000000 : ℚ) : ℝ) ≤ Real.log (801 : ℕ) / 2 := by
    have h := (log_br_801).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (801 : ℕ) / 2 ≤ ((6685861/2000000 : ℚ) : ℝ) := by
    have h := (log_br_801).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7968951/12500000) (δ := 5711/200000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_802 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (802 : ℕ) / 2)) - ((-1318381/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33435543/10000000 : ℚ) : ℝ) ≤ Real.log (802 : ℕ) / 2 := by
    have h := (log_br_802).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (802 : ℕ) / 2 ≤ ((66871087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_802).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4594069/10000000) (δ := 285653/10000000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_803 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (803 : ℕ) / 2)) - ((4301797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66883547/20000000 : ℚ) : ℝ) ≤ Real.log (803 : ℕ) / 2 := by
    have h := (log_br_803).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (803 : ℕ) / 2 ≤ ((16720887/5000000 : ℚ) : ℝ) := by
    have h := (log_br_803).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28152613/100000000) (δ := 5711/200000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_804 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (804 : ℕ) / 2)) - ((4574583/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8361999/2500000 : ℚ) : ℝ) ≤ Real.log (804 : ℕ) / 2 := by
    have h := (log_br_804).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (804 : ℕ) / 2 ≤ ((66895993/20000000 : ℚ) : ℝ) := by
    have h := (log_br_804).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -83099/800000) (δ := 285653/10000000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_805 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (805 : ℕ) / 2)) - ((74767/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33454211/10000000 : ℚ) : ℝ) ≤ Real.log (805 : ℕ) / 2 := by
    have h := (log_br_805).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (805 : ℕ) / 2 ≤ ((66908423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_805).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 147129/2000000) (δ := 285653/10000000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_806 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (806 : ℕ) / 2)) - ((1344113/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66920837/20000000 : ℚ) : ℝ) ≤ Real.log (806 : ℕ) / 2 := by
    have h := (log_br_806).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (806 : ℕ) / 2 ≤ ((33460419/10000000 : ℚ) : ℝ) := by
    have h := (log_br_806).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12539431/50000000) (δ := 5711/200000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_807 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (807 : ℕ) / 2)) - ((-174851/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16733309/5000000 : ℚ) : ℝ) ≤ Real.log (807 : ℕ) / 2 := by
    have h := (log_br_807).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (807 : ℕ) / 2 ≤ ((66933237/20000000 : ℚ) : ℝ) := by
    have h := (log_br_807).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8555687/20000000) (δ := 285653/10000000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_808 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (808 : ℕ) / 2)) - ((-3748033/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3347281/1000000 : ℚ) : ℝ) ≤ Real.log (808 : ℕ) / 2 := by
    have h := (log_br_808).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (808 : ℕ) / 2 ≤ ((66945621/20000000 : ℚ) : ℝ) := by
    have h := (log_br_808).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12091319/20000000) (δ := 285653/10000000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_809 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (809 : ℕ) / 2)) - ((-1999709/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66957989/20000000 : ℚ) : ℝ) ≤ Real.log (809 : ℕ) / 2 := by
    have h := (log_br_809).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (809 : ℕ) / 2 ≤ ((6695799/2000000 : ℚ) : ℝ) := by
    have h := (log_br_809).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39056671/50000000) (δ := 5711/200000000) 1142 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_810 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (810 : ℕ) / 2)) - ((-7723287/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33485171/10000000 : ℚ) : ℝ) ≤ Real.log (810 : ℕ) / 2 := by
    have h := (log_br_810).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (810 : ℕ) / 2 ≤ ((66970343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_810).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61332383/100000000) (δ := 11421/400000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_811 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (811 : ℕ) / 2)) - ((-1770607/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1674567/500000 : ℚ) : ℝ) ≤ Real.log (811 : ℕ) / 2 := by
    have h := (log_br_811).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (811 : ℕ) / 2 ≤ ((66982681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_811).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2732493/6250000) (δ := 11421/400000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_812 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (812 : ℕ) / 2)) - ((2508851/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66995003/20000000 : ℚ) : ℝ) ≤ Real.log (812 : ℕ) / 2 := by
    have h := (log_br_812).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (812 : ℕ) / 2 ≤ ((16748751/5000000 : ℚ) : ℝ) := by
    have h := (log_br_812).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13064403/50000000) (δ := 142839/5000000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_813 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (813 : ℕ) / 2)) - ((588727/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67007311/20000000 : ℚ) : ℝ) ≤ Real.log (813 : ℕ) / 2 := by
    have h := (log_br_813).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (813 : ℕ) / 2 ≤ ((4187957/1250000 : ℚ) : ℝ) := by
    have h := (log_br_813).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -267473/3125000) (δ := 142839/5000000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_814 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (814 : ℕ) / 2)) - ((9360701/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67019603/20000000 : ℚ) : ℝ) ≤ Real.log (814 : ℕ) / 2 := by
    have h := (log_br_814).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (814 : ℕ) / 2 ≤ ((16754901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_814).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4493847/50000000) (δ := 142839/5000000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_815 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (815 : ℕ) / 2)) - ((4883647/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67031881/20000000 : ℚ) : ℝ) ≤ Real.log (815 : ℕ) / 2 := by
    have h := (log_br_815).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (815 : ℕ) / 2 ≤ ((33515941/10000000 : ℚ) : ℝ) := by
    have h := (log_br_815).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26514539/100000000) (δ := 142839/5000000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_816 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (816 : ℕ) / 2)) - ((-1888053/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67044143/20000000 : ℚ) : ℝ) ≤ Real.log (816 : ℕ) / 2 := by
    have h := (log_br_816).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (816 : ℕ) / 2 ≤ ((4190259/1250000 : ℚ) : ℝ) := by
    have h := (log_br_816).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2751159/6250000) (δ := 142839/5000000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_817 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (817 : ℕ) / 2)) - ((-7765989/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6705639/2000000 : ℚ) : ℝ) ≤ Real.log (817 : ℕ) / 2 := by
    have h := (log_br_817).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (817 : ℕ) / 2 ≤ ((67056391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_817).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61501137/100000000) (δ := 11421/400000000) 1142 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_818 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (818 : ℕ) / 2)) - ((-4999281/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67068623/20000000 : ℚ) : ℝ) ≤ Real.log (818 : ℕ) / 2 := by
    have h := (log_br_818).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (818 : ℕ) / 2 ≤ ((4191789/1250000 : ℚ) : ℝ) := by
    have h := (log_br_818).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4882243/6250000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_819 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (819 : ℕ) / 2)) - ((-944237/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1677021/500000 : ℚ) : ℝ) ≤ Real.log (819 : ℕ) / 2 := by
    have h := (log_br_819).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (819 : ℕ) / 2 ≤ ((67080841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_819).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60676121/100000000) (δ := 142803/5000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_820 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (820 : ℕ) / 2)) - ((-1587823/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67093043/20000000 : ℚ) : ℝ) ≤ Real.log (820 : ℕ) / 2 := by
    have h := (log_br_820).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (820 : ℕ) / 2 ≤ ((16773261/5000000 : ℚ) : ℝ) := by
    have h := (log_br_820).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21628169/50000000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_821 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (821 : ℕ) / 2)) - ((1277779/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67105231/20000000 : ℚ) : ℝ) ≤ Real.log (821 : ℕ) / 2 := by
    have h := (log_br_821).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (821 : ℕ) / 2 ≤ ((4194077/1250000 : ℚ) : ℝ) := by
    have h := (log_br_821).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1616123/6250000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_822 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (822 : ℕ) / 2)) - ((9429887/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67117403/20000000 : ℚ) : ℝ) ≤ Real.log (822 : ℕ) / 2 := by
    have h := (log_br_822).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (822 : ℕ) / 2 ≤ ((16779351/5000000 : ℚ) : ℝ) := by
    have h := (log_br_822).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4241219/50000000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_823 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (823 : ℕ) / 2)) - ((937653/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33564781/10000000 : ℚ) : ℝ) ≤ Real.log (823 : ℕ) / 2 := by
    have h := (log_br_823).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (823 : ℕ) / 2 ≤ ((67129563/20000000 : ℚ) : ℝ) := by
    have h := (log_br_823).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4437267/50000000) (δ := 142803/5000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_824 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (824 : ℕ) / 2)) - ((998009/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13428341/4000000 : ℚ) : ℝ) ≤ Real.log (824 : ℕ) / 2 := by
    have h := (log_br_824).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (824 : ℕ) / 2 ≤ ((33570853/10000000 : ℚ) : ℝ) := by
    have h := (log_br_824).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26208667/100000000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_825 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (825 : ℕ) / 2)) - ((-846203/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67153833/20000000 : ℚ) : ℝ) ≤ Real.log (825 : ℕ) / 2 := by
    have h := (log_br_825).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (825 : ℕ) / 2 ≤ ((33576917/10000000 : ℚ) : ℝ) := by
    have h := (log_br_825).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 43521387/100000000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_826 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (826 : ℕ) / 2)) - ((-118593/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67165947/20000000 : ℚ) : ℝ) ≤ Real.log (826 : ℕ) / 2 := by
    have h := (log_br_826).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (826 : ℕ) / 2 ≤ ((16791487/5000000 : ℚ) : ℝ) := by
    have h := (log_br_826).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30407061/50000000) (δ := 285597/10000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_827 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (827 : ℕ) / 2)) - ((-2499587/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33589023/10000000 : ℚ) : ℝ) ≤ Real.log (827 : ℕ) / 2 := by
    have h := (log_br_827).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (827 : ℕ) / 2 ≤ ((67178047/20000000 : ℚ) : ℝ) := by
    have h := (log_br_827).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19521361/25000000) (δ := 142803/5000000000) 1142 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_828 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (828 : ℕ) / 2)) - ((-7826537/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67190131/20000000 : ℚ) : ℝ) ≤ Real.log (828 : ℕ) / 2 := by
    have h := (log_br_828).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (828 : ℕ) / 2 ≤ ((16797533/5000000 : ℚ) : ℝ) := by
    have h := (log_br_828).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61742851/100000000) (δ := 142767/5000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_829 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (829 : ℕ) / 2)) - ((-2081867/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67202201/20000000 : ℚ) : ℝ) ≤ Real.log (829 : ℕ) / 2 := by
    have h := (log_br_829).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (829 : ℕ) / 2 ≤ ((33601101/10000000 : ℚ) : ℝ) := by
    have h := (log_br_829).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22256463/50000000) (δ := 142767/5000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_830 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (830 : ℕ) / 2)) - ((1151513/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67214257/20000000 : ℚ) : ℝ) ≤ Real.log (830 : ℕ) / 2 := by
    have h := (log_br_830).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (830 : ℕ) / 2 ≤ ((33607129/10000000 : ℚ) : ℝ) := by
    have h := (log_br_830).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13651493/50000000) (δ := 142767/5000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_831 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (831 : ℕ) / 2)) - ((459623/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67226297/20000000 : ℚ) : ℝ) ≤ Real.log (831 : ℕ) / 2 := by
    have h := (log_br_831).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (831 : ℕ) / 2 ≤ ((33613149/10000000 : ℚ) : ℝ) := by
    have h := (log_br_831).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5057943/50000000) (δ := 142767/5000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_832 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (832 : ℕ) / 2)) - ((1200589/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16809581/5000000 : ℚ) : ℝ) ≤ Real.log (832 : ℕ) / 2 := by
    have h := (log_br_832).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (832 : ℕ) / 2 ≤ ((2689533/800000 : ℚ) : ℝ) := by
    have h := (log_br_832).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7052657/100000000) (δ := 285669/10000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_833 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (833 : ℕ) / 2)) - ((354347/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2101573/625000 : ℚ) : ℝ) ≤ Real.log (833 : ℕ) / 2 := by
    have h := (log_br_833).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (833 : ℕ) / 2 ≤ ((67250337/20000000 : ℚ) : ℝ) := by
    have h := (log_br_833).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24199787/100000000) (δ := 285669/10000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_834 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (834 : ℕ) / 2)) - ((-821881/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33631167/10000000 : ℚ) : ℝ) ≤ Real.log (834 : ℕ) / 2 := by
    have h := (log_br_834).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (834 : ℕ) / 2 ≤ ((13452467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_834).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10331733/25000000) (δ := 285669/10000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_835 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (835 : ℕ) / 2)) - ((-6936257/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67274317/20000000 : ℚ) : ℝ) ≤ Real.log (835 : ℕ) / 2 := by
    have h := (log_br_835).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (835 : ℕ) / 2 ≤ ((33637159/10000000 : ℚ) : ℝ) := by
    have h := (log_br_835).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7304083/12500000) (δ := 142767/5000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_836 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (836 : ℕ) / 2)) - ((-4963529/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33643143/10000000 : ℚ) : ℝ) ≤ Real.log (836 : ℕ) / 2 := by
    have h := (log_br_836).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (836 : ℕ) / 2 ≤ ((67286287/20000000 : ℚ) : ℝ) := by
    have h := (log_br_836).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18879603/25000000) (δ := 285669/10000000000) 1142 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_837 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (837 : ℕ) / 2)) - ((-8463417/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((210307/62500 : ℚ) : ℝ) ≤ Real.log (837 : ℕ) / 2 := by
    have h := (log_br_837).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (837 : ℕ) / 2 ≤ ((67298241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_837).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32248443/50000000) (δ := 285541/10000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_838 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (838 : ℕ) / 2)) - ((-3214383/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67310181/20000000 : ℚ) : ℝ) ≤ Real.log (838 : ℕ) / 2 := by
    have h := (log_br_838).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (838 : ℕ) / 2 ≤ ((33655091/10000000 : ℚ) : ℝ) := by
    have h := (log_br_838).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -47451109/100000000) (δ := 142831/5000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_839 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (839 : ℕ) / 2)) - ((3463961/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67322107/20000000 : ℚ) : ℝ) ≤ Real.log (839 : ℕ) / 2 := by
    have h := (log_br_839).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (839 : ℕ) / 2 ≤ ((16830527/5000000 : ℚ) : ℝ) := by
    have h := (log_br_839).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3803343/12500000) (δ := 142831/5000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_840 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (840 : ℕ) / 2)) - ((107409/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33667009/10000000 : ℚ) : ℝ) ≤ Real.log (840 : ℕ) / 2 := by
    have h := (log_br_840).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (840 : ℕ) / 2 ≤ ((67334019/20000000 : ℚ) : ℝ) := by
    have h := (log_br_840).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13423791/100000000) (δ := 285541/10000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_841 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (841 : ℕ) / 2)) - ((2474687/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/5000000 : ℚ) : ℝ) ≤ Real.log (841 : ℕ) / 2 := by
    have h := (log_br_841).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (841 : ℕ) / 2 ≤ ((67345917/20000000 : ℚ) : ℝ) := by
    have h := (log_br_841).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 890151/25000000) (δ := 285541/10000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_842 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (842 : ℕ) / 2)) - ((6814893/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((336789/100000 : ℚ) : ℝ) ≤ Real.log (842 : ℕ) / 2 := by
    have h := (log_br_842).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (842 : ℕ) / 2 ≤ ((67357801/20000000 : ℚ) : ℝ) := by
    have h := (log_br_842).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10262507/50000000) (δ := 285541/10000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_843 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (843 : ℕ) / 2)) - ((144027/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67369669/20000000 : ℚ) : ℝ) ≤ Real.log (843 : ℕ) / 2 := by
    have h := (log_br_843).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (843 : ℕ) / 2 ≤ ((6736967/2000000 : ℚ) : ℝ) := by
    have h := (log_br_843).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37468011/100000000) (δ := 142831/5000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_844 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (844 : ℕ) / 2)) - ((-5686343/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16845381/5000000 : ℚ) : ℝ) ≤ Real.log (844 : ℕ) / 2 := by
    have h := (log_br_844).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (844 : ℕ) / 2 ≤ ((2695261/800000 : ℚ) : ℝ) := by
    have h := (log_br_844).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3399439/6250000) (δ := 285541/10000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_845 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (845 : ℕ) / 2)) - ((-4791543/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33696683/10000000 : ℚ) : ℝ) ≤ Real.log (845 : ℕ) / 2 := by
    have h := (log_br_845).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (845 : ℕ) / 2 ≤ ((67393367/20000000 : ℚ) : ℝ) := by
    have h := (log_br_845).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71295479/100000000) (δ := 285541/10000000000) 1142 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_846 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (846 : ℕ) / 2)) - ((-2316481/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67405193/20000000 : ℚ) : ℝ) ≤ Real.log (846 : ℕ) / 2 := by
    have h := (log_br_846).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (846 : ℕ) / 2 ≤ ((33702597/10000000 : ℚ) : ℝ) := by
    have h := (log_br_846).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -68901111/100000000) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_847 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (847 : ℕ) / 2)) - ((-2444053/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33708503/10000000 : ℚ) : ℝ) ≤ Real.log (847 : ℕ) / 2 := by
    have h := (log_br_847).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (847 : ℕ) / 2 ≤ ((67417007/20000000 : ℚ) : ℝ) := by
    have h := (log_br_847).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26019027/50000000) (δ := 285591/10000000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_848 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (848 : ℕ) / 2)) - ((811663/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33714403/10000000 : ℚ) : ℝ) ≤ Real.log (848 : ℕ) / 2 := by
    have h := (log_br_848).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (848 : ℕ) / 2 ≤ ((67428807/20000000 : ℚ) : ℝ) := by
    have h := (log_br_848).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17596777/50000000) (δ := 285591/10000000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_849 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (849 : ℕ) / 2)) - ((1854881/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67440591/20000000 : ℚ) : ℝ) ≤ Real.log (849 : ℕ) / 2 := by
    have h := (log_br_849).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (849 : ℕ) / 2 ≤ ((4215037/1250000 : ℚ) : ℝ) := by
    have h := (log_br_849).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9185233/50000000) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_850 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (850 : ℕ) / 2)) - ((9980389/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67452363/20000000 : ℚ) : ℝ) ≤ Real.log (850 : ℕ) / 2 := by
    have h := (log_br_850).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (850 : ℕ) / 2 ≤ ((16863091/5000000 : ℚ) : ℝ) := by
    have h := (log_br_850).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -97871/6250000) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_851 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (851 : ℕ) / 2)) - ((8203667/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67464121/20000000 : ℚ) : ℝ) ≤ Real.log (851 : ℕ) / 2 := by
    have h := (log_br_851).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (851 : ℕ) / 2 ≤ ((33732061/10000000 : ℚ) : ℝ) := by
    have h := (log_br_851).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15218609/100000000) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_852 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (852 : ℕ) / 2)) - ((2873601/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13495173/4000000 : ℚ) : ℝ) ≤ Real.log (852 : ℕ) / 2 := by
    have h := (log_br_852).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (852 : ℕ) / 2 ≤ ((33737933/10000000 : ℚ) : ℝ) := by
    have h := (log_br_852).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31983169/100000000) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_853 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (853 : ℕ) / 2)) - ((-3693537/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13497519/4000000 : ℚ) : ℝ) ≤ Real.log (853 : ℕ) / 2 := by
    have h := (log_br_853).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (853 : ℕ) / 2 ≤ ((16871899/5000000 : ℚ) : ℝ) := by
    have h := (log_br_853).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 761371/1562500) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_854 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (854 : ℕ) / 2)) - ((-8660751/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67499311/20000000 : ℚ) : ℝ) ≤ Real.log (854 : ℕ) / 2 := by
    have h := (log_br_854).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (854 : ℕ) / 2 ≤ ((4218707/1250000 : ℚ) : ℝ) := by
    have h := (log_br_854).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32726167/50000000) (δ := 71403/2500000000) 1142 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_855 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (855 : ℕ) / 2)) - ((-1236929/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33755507/10000000 : ℚ) : ℝ) ≤ Real.log (855 : ℕ) / 2 := by
    have h := (log_br_855).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (855 : ℕ) / 2 ≤ ((13502203/4000000 : ℚ) : ℝ) := by
    have h := (log_br_855).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37460633/50000000) (δ := 71421/2500000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_856 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (856 : ℕ) / 2)) - ((-137583/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67522703/20000000 : ℚ) : ℝ) ≤ Real.log (856 : ℕ) / 2 := by
    have h := (log_br_856).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (856 : ℕ) / 2 ≤ ((4220169/1250000 : ℚ) : ℝ) := by
    have h := (log_br_856).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -58235219/100000000) (δ := 285519/10000000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_857 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (857 : ℕ) / 2)) - ((-183567/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67534379/20000000 : ℚ) : ℝ) ≤ Real.log (857 : ℕ) / 2 := by
    have h := (log_br_857).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (857 : ℕ) / 2 ≤ ((3376719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_857).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41567729/100000000) (δ := 285519/10000000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_858 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (858 : ℕ) / 2)) - ((678671/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1688651/500000 : ℚ) : ℝ) ≤ Real.log (858 : ℕ) / 2 := by
    have h := (log_br_858).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (858 : ℕ) / 2 ≤ ((67546041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_858).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24921651/100000000) (δ := 71421/2500000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_859 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (859 : ℕ) / 2)) - ((4727437/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67557689/20000000 : ℚ) : ℝ) ≤ Real.log (859 : ℕ) / 2 := by
    have h := (log_br_859).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (859 : ℕ) / 2 ≤ ((6755769/2000000 : ℚ) : ℝ) := by
    have h := (log_br_859).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -259147/3125000) (δ := 285519/10000000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_860 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (860 : ℕ) / 2)) - ((2362997/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67569323/20000000 : ℚ) : ℝ) ≤ Real.log (860 : ℕ) / 2 := by
    have h := (log_br_860).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (860 : ℕ) / 2 ≤ ((16892331/5000000 : ℚ) : ℝ) := by
    have h := (log_br_860).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8314831/100000000) (δ := 285519/10000000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_861 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (861 : ℕ) / 2)) - ((5434881/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13516189/4000000 : ℚ) : ℝ) ≤ Real.log (861 : ℕ) / 2 := by
    have h := (log_br_861).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (861 : ℕ) / 2 ≤ ((33790473/10000000 : ℚ) : ℝ) := by
    have h := (log_br_861).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6226309/25000000) (δ := 285519/10000000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_862 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (862 : ℕ) / 2)) - ((-440293/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8449069/2500000 : ℚ) : ℝ) ≤ Real.log (862 : ℕ) / 2 := by
    have h := (log_br_862).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (862 : ℕ) / 2 ≤ ((67592553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_862).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 41474229/100000000) (δ := 71421/2500000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_863 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (863 : ℕ) / 2)) - ((-6817779/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33802073/10000000 : ℚ) : ℝ) ≤ Real.log (863 : ℕ) / 2 := by
    have h := (log_br_863).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (863 : ℕ) / 2 ≤ ((67604147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_863).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7253083/12500000) (δ := 71421/2500000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_864 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (864 : ℕ) / 2)) - ((-1234167/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67615727/20000000 : ℚ) : ℝ) ≤ Real.log (864 : ℕ) / 2 := by
    have h := (log_br_864).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (864 : ℕ) / 2 ≤ ((4225983/1250000 : ℚ) : ℝ) := by
    have h := (log_br_864).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 74556541/100000000) (δ := 285519/10000000000) 1142 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_865 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (865 : ℕ) / 2)) - ((-4385029/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13525459/4000000 : ℚ) : ℝ) ≤ Real.log (865 : ℕ) / 2 := by
    have h := (log_br_865).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (865 : ℕ) / 2 ≤ ((2113353/625000 : ℚ) : ℝ) := by
    have h := (log_br_865).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16502443/25000000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_866 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (866 : ℕ) / 2)) - ((-199241/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67638849/20000000 : ℚ) : ℝ) ≤ Real.log (866 : ℕ) / 2 := by
    have h := (log_br_866).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (866 : ℕ) / 2 ≤ ((1352777/400000 : ℚ) : ℝ) := by
    have h := (log_br_866).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49516437/100000000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_867 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (867 : ℕ) / 2)) - ((493011/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67650389/20000000 : ℚ) : ℝ) ≤ Real.log (867 : ℕ) / 2 := by
    have h := (log_br_867).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (867 : ℕ) / 2 ≤ ((6765039/2000000 : ℚ) : ℝ) := by
    have h := (log_br_867).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33043087/100000000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_868 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (868 : ℕ) / 2)) - ((7878571/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67661917/20000000 : ℚ) : ℝ) ≤ Real.log (868 : ℕ) / 2 := by
    have h := (log_br_868).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (868 : ℕ) / 2 ≤ ((33830959/10000000 : ℚ) : ℝ) := by
    have h := (log_br_868).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16586867/100000000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_869 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (869 : ℕ) / 2)) - ((4999909/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67673431/20000000 : ℚ) : ℝ) ≤ Real.log (869 : ℕ) / 2 := by
    have h := (log_br_869).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (869 : ℕ) / 2 ≤ ((8459179/2500000 : ℚ) : ℝ) := by
    have h := (log_br_869).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18829/12500000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_870 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (870 : ℕ) / 2)) - ((795671/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16921233/5000000 : ℚ) : ℝ) ≤ Real.log (870 : ℕ) / 2 := by
    have h := (log_br_870).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (870 : ℕ) / 2 ≤ ((67684933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_870).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8133523/50000000) (δ := 71389/2500000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_871 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (871 : ℕ) / 2)) - ((2611437/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67696419/20000000 : ℚ) : ℝ) ≤ Real.log (871 : ℕ) / 2 := by
    have h := (log_br_871).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (871 : ℕ) / 2 ≤ ((3384821/1000000 : ℚ) : ℝ) := by
    have h := (log_br_871).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16332369/50000000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_872 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (872 : ℕ) / 2)) - ((-3811277/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33853947/10000000 : ℚ) : ℝ) ≤ Real.log (872 : ℕ) / 2 := by
    have h := (log_br_872).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (872 : ℕ) / 2 ≤ ((13541579/4000000 : ℚ) : ℝ) := by
    have h := (log_br_872).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 49045301/100000000) (δ := 71389/2500000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_873 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (873 : ℕ) / 2)) - ((-8651447/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13543871/4000000 : ℚ) : ℝ) ≤ Real.log (873 : ℕ) / 2 := by
    have h := (log_br_873).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (873 : ℕ) / 2 ≤ ((16929839/5000000 : ℚ) : ℝ) := by
    have h := (log_br_873).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32702939/50000000) (δ := 285647/10000000000) 1142 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_874 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (874 : ℕ) / 2)) - ((-9917779/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67730803/20000000 : ℚ) : ℝ) ≤ Real.log (874 : ℕ) / 2 := by
    have h := (log_br_874).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (874 : ℕ) / 2 ≤ ((16932701/5000000 : ℚ) : ℝ) := by
    have h := (log_br_874).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37665867/50000000) (δ := 71407/2500000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_875 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (875 : ℕ) / 2)) - ((-221883/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33871119/10000000 : ℚ) : ℝ) ≤ Real.log (875 : ℕ) / 2 := by
    have h := (log_br_875).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (875 : ℕ) / 2 ≤ ((67742239/20000000 : ℚ) : ℝ) := by
    have h := (log_br_875).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3688017/6250000) (δ := 11423/400000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_876 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (876 : ℕ) / 2)) - ((-136907/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3387683/1000000 : ℚ) : ℝ) ≤ Real.log (876 : ℕ) / 2 := by
    have h := (log_br_876).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (876 : ℕ) / 2 ≤ ((67753661/20000000 : ℚ) : ℝ) := by
    have h := (log_br_876).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -42703367/100000000) (δ := 11423/400000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_877 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (877 : ℕ) / 2)) - ((4917649/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67765069/20000000 : ℚ) : ℝ) ≤ Real.log (877 : ℕ) / 2 := by
    have h := (log_br_877).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (877 : ℕ) / 2 ≤ ((6776507/2000000 : ℚ) : ℝ) := by
    have h := (log_br_877).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26417019/100000000) (δ := 71407/2500000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_878 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (878 : ℕ) / 2)) - ((9187201/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13555293/4000000 : ℚ) : ℝ) ≤ Real.log (878 : ℕ) / 2 := by
    have h := (log_br_878).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (878 : ℕ) / 2 ≤ ((33888233/10000000 : ℚ) : ℝ) := by
    have h := (log_br_878).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10149229/100000000) (δ := 71407/2500000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_879 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (879 : ℕ) / 2)) - ((4851897/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8473481/2500000 : ℚ) : ℝ) ≤ Real.log (879 : ℕ) / 2 := by
    have h := (log_br_879).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (879 : ℕ) / 2 ≤ ((67787849/20000000 : ℚ) : ℝ) := by
    have h := (log_br_879).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6100003/100000000) (δ := 11423/400000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_880 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (880 : ℕ) / 2)) - ((1253713/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67799219/20000000 : ℚ) : ℝ) ≤ Real.log (880 : ℕ) / 2 := by
    have h := (log_br_880).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (880 : ℕ) / 2 ≤ ((3389961/1000000 : ℚ) : ℝ) := by
    have h := (log_br_880).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11166053/50000000) (δ := 71407/2500000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_881 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (881 : ℕ) / 2)) - ((290233/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4238161/1250000 : ℚ) : ℝ) ≤ Real.log (881 : ℕ) / 2 := by
    have h := (log_br_881).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (881 : ℕ) / 2 ≤ ((67810577/20000000 : ℚ) : ℝ) := by
    have h := (log_br_881).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38544223/100000000) (δ := 11423/400000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_882 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (882 : ℕ) / 2)) - ((-362493/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((423887/125000 : ℚ) : ℝ) ≤ Real.log (882 : ℕ) / 2 := by
    have h := (log_br_882).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (882 : ℕ) / 2 ≤ ((67821921/20000000 : ℚ) : ℝ) := by
    have h := (log_br_882).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54737783/100000000) (δ := 11423/400000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_883 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (883 : ℕ) / 2)) - ((-9538397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16958313/5000000 : ℚ) : ℝ) ≤ Real.log (883 : ℕ) / 2 := by
    have h := (log_br_883).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (883 : ℕ) / 2 ≤ ((67833253/20000000 : ℚ) : ℝ) := by
    have h := (log_br_883).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70914213/100000000) (δ := 11423/400000000) 1142 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_884 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (884 : ℕ) / 2)) - ((-376937/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6784457/2000000 : ℚ) : ℝ) ≤ Real.log (884 : ℕ) / 2 := by
    have h := (log_br_884).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (884 : ℕ) / 2 ≤ ((67844571/20000000 : ℚ) : ℝ) := by
    have h := (log_br_884).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35004487/50000000) (δ := 2857/100000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_885 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (885 : ℕ) / 2)) - ((-5513571/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16963969/5000000 : ℚ) : ℝ) ≤ Real.log (885 : ℕ) / 2 := by
    have h := (log_br_885).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (885 : ℕ) / 2 ≤ ((67855877/20000000 : ℚ) : ℝ) := by
    have h := (log_br_885).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53869659/100000000) (δ := 2857/100000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_886 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (886 : ℕ) / 2)) - ((608027/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67867169/20000000 : ℚ) : ℝ) ≤ Real.log (886 : ℕ) / 2 := by
    have h := (log_br_886).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (886 : ℕ) / 2 ≤ ((6786717/2000000 : ℚ) : ℝ) := by
    have h := (log_br_886).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18874451/50000000) (δ := 285503/10000000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_887 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (887 : ℕ) / 2)) - ((404987/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67878449/20000000 : ℚ) : ℝ) ≤ Real.log (887 : ℕ) / 2 := by
    have h := (log_br_887).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (887 : ℕ) / 2 ≤ ((1357569/400000 : ℚ) : ℝ) := by
    have h := (log_br_887).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10823351/50000000) (δ := 285503/10000000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_888 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (888 : ℕ) / 2)) - ((1950713/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67889717/20000000 : ℚ) : ℝ) ≤ Real.log (888 : ℕ) / 2 := by
    have h := (log_br_888).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (888 : ℕ) / 2 ≤ ((33944859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_888).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -173801/3125000) (δ := 285503/10000000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_889 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (889 : ℕ) / 2)) - ((9130093/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16975243/5000000 : ℚ) : ℝ) ≤ Real.log (889 : ℕ) / 2 := by
    have h := (log_br_889).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (889 : ℕ) / 2 ≤ ((67900973/20000000 : ℚ) : ℝ) := by
    have h := (log_br_889).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10504881/100000000) (δ := 2857/100000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_890 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (890 : ℕ) / 2)) - ((4870273/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33956107/10000000 : ℚ) : ℝ) ≤ Real.log (890 : ℕ) / 2 := by
    have h := (log_br_890).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (890 : ℕ) / 2 ≤ ((13582443/4000000 : ℚ) : ℝ) := by
    have h := (log_br_890).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6638209/25000000) (δ := 2857/100000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_891 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (891 : ℕ) / 2)) - ((-1321623/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16980861/5000000 : ℚ) : ℝ) ≤ Real.log (891 : ℕ) / 2 := by
    have h := (log_br_891).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (891 : ℕ) / 2 ≤ ((13584689/4000000 : ℚ) : ℝ) := by
    have h := (log_br_891).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42583661/100000000) (δ := 2857/100000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_892 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (892 : ℕ) / 2)) - ((-139663/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67934661/20000000 : ℚ) : ℝ) ≤ Real.log (892 : ℕ) / 2 := by
    have h := (log_br_892).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (892 : ℕ) / 2 ≤ ((33967331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_892).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7324491/12500000) (δ := 285503/10000000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_893 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (893 : ℕ) / 2)) - ((-2468857/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13589173/4000000 : ℚ) : ℝ) ≤ Real.log (893 : ℕ) / 2 := by
    have h := (log_br_893).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (893 : ℕ) / 2 ≤ ((33972933/10000000 : ℚ) : ℝ) := by
    have h := (log_br_893).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37294819/50000000) (δ := 285503/10000000000) 1142 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_894 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (894 : ℕ) / 2)) - ((-2216267/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67957057/20000000 : ℚ) : ℝ) ≤ Real.log (894 : ℕ) / 2 := by
    have h := (log_br_894).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (894 : ℕ) / 2 ≤ ((33978529/10000000 : ℚ) : ℝ) := by
    have h := (log_br_894).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13302683/20000000) (δ := 4463/156250000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_895 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (895 : ℕ) / 2)) - ((-2180959/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67968237/20000000 : ℚ) : ℝ) ≤ Real.log (895 : ℕ) / 2 := by
    have h := (log_br_895).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (895 : ℕ) / 2 ≤ ((33984119/10000000 : ℚ) : ℝ) := by
    have h := (log_br_895).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10110793/20000000) (δ := 4463/156250000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_896 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (896 : ℕ) / 2)) - ((1851981/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16994851/5000000 : ℚ) : ℝ) ≤ Real.log (896 : ℕ) / 2 := by
    have h := (log_br_896).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (896 : ℕ) / 2 ≤ ((13595881/4000000 : ℚ) : ℝ) := by
    have h := (log_br_896).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2163317/6250000) (δ := 285571/10000000000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_897 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (897 : ℕ) / 2)) - ((3666513/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33995279/10000000 : ℚ) : ℝ) ≤ Real.log (897 : ℕ) / 2 := by
    have h := (log_br_897).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (897 : ℕ) / 2 ≤ ((67990559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_897).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18690737/100000000) (δ := 285571/10000000000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_898 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (898 : ℕ) / 2)) - ((9937991/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((680017/200000 : ℚ) : ℝ) ≤ Real.log (898 : ℕ) / 2 := by
    have h := (log_br_898).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (898 : ℕ) / 2 ≤ ((68001701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_898).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -696383/25000000) (δ := 285571/10000000000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_899 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (899 : ℕ) / 2)) - ((4328869/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6801283/2000000 : ℚ) : ℝ) ≤ Real.log (899 : ℕ) / 2 := by
    have h := (log_br_899).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (899 : ℕ) / 2 ≤ ((68012831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_899).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13102543/100000000) (δ := 285571/10000000000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_900 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (900 : ℕ) / 2)) - ((4003639/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68023947/20000000 : ℚ) : ℝ) ≤ Real.log (900 : ℕ) / 2 := by
    have h := (log_br_900).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (900 : ℕ) / 2 ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := (log_br_900).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1448603/5000000) (δ := 4463/156250000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_901 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (901 : ℕ) / 2)) - ((-2203581/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17008763/5000000 : ℚ) : ℝ) ≤ Real.log (901 : ℕ) / 2 := by
    have h := (log_br_901).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (901 : ℕ) / 2 ≤ ((68035053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_901).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 350191/781250) (δ := 285571/10000000000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_902 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (902 : ℕ) / 2)) - ((-943699/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13609229/4000000 : ℚ) : ℝ) ≤ Real.log (902 : ℕ) / 2 := by
    have h := (log_br_902).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (902 : ℕ) / 2 ≤ ((34023073/10000000 : ℚ) : ℝ) := by
    have h := (log_br_902).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12131941/20000000) (δ := 4463/156250000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_903 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (903 : ℕ) / 2)) - ((-4982979/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722289/800000 : ℚ) : ℝ) ≤ Real.log (903 : ℕ) / 2 := by
    have h := (log_br_903).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (903 : ℕ) / 2 ≤ ((34028613/10000000 : ℚ) : ℝ) := by
    have h := (log_br_903).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15295281/20000000) (δ := 4463/156250000) 1142 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_904 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (904 : ℕ) / 2)) - ((-4264069/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68068293/20000000 : ℚ) : ℝ) ≤ Real.log (904 : ℕ) / 2 := by
    have h := (log_br_904).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (904 : ℕ) / 2 ≤ ((34034147/10000000 : ℚ) : ℝ) := by
    have h := (log_br_904).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -64803657/100000000) (δ := 285643/10000000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_905 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (905 : ℕ) / 2)) - ((-29706/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68079349/20000000 : ℚ) : ℝ) ≤ Real.log (905 : ℕ) / 2 := by
    have h := (log_br_905).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (905 : ℕ) / 2 ≤ ((1361587/400000 : ℚ) : ℝ) := by
    have h := (log_br_905).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49021217/100000000) (δ := 285643/10000000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_906 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (906 : ℕ) / 2)) - ((1191233/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68090393/20000000 : ℚ) : ℝ) ≤ Real.log (906 : ℕ) / 2 := by
    have h := (log_br_906).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (906 : ℕ) / 2 ≤ ((34045197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_906).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33255907/100000000) (δ := 285643/10000000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_907 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (907 : ℕ) / 2)) - ((3823031/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4256339/1250000 : ℚ) : ℝ) ≤ Real.log (907 : ℕ) / 2 := by
    have h := (log_br_907).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (907 : ℕ) / 2 ≤ ((2724057/800000 : ℚ) : ℝ) := by
    have h := (log_br_907).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3501831/20000000) (δ := 7139/250000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_908 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (908 : ℕ) / 2)) - ((9974677/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68112443/20000000 : ℚ) : ℝ) ≤ Real.log (908 : ℕ) / 2 := by
    have h := (log_br_908).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (908 : ℕ) / 2 ≤ ((17028111/5000000 : ℚ) : ℝ) := by
    have h := (log_br_908).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -444883/25000000) (δ := 285643/10000000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_909 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (909 : ℕ) / 2)) - ((1697353/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1362469/400000 : ℚ) : ℝ) ≤ Real.log (909 : ℕ) / 2 := by
    have h := (log_br_909).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (909 : ℕ) / 2 ≤ ((68123451/20000000 : ℚ) : ℝ) := by
    have h := (log_br_909).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 87081/625000) (δ := 7139/250000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_910 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (910 : ℕ) / 2)) - ((3761739/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13626889/4000000 : ℚ) : ℝ) ≤ Real.log (910 : ℕ) / 2 := by
    have h := (log_br_910).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (910 : ℕ) / 2 ≤ ((34067223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_910).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29628323/100000000) (δ := 285643/10000000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_911 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (911 : ℕ) / 2)) - ((-1195631/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17036357/5000000 : ℚ) : ℝ) ≤ Real.log (911 : ℕ) / 2 := by
    have h := (log_br_911).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (911 : ℕ) / 2 ≤ ((68145429/20000000 : ℚ) : ℝ) := by
    have h := (log_br_911).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9061311/20000000) (δ := 7139/250000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_912 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (912 : ℕ) / 2)) - ((-1907449/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68156399/20000000 : ℚ) : ℝ) ≤ Real.log (912 : ℕ) / 2 := by
    have h := (log_br_912).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (912 : ℕ) / 2 ≤ ((170391/50000 : ℚ) : ℝ) := by
    have h := (log_br_912).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30483829/50000000) (δ := 285643/10000000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_913 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (913 : ℕ) / 2)) - ((-311571/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34083679/10000000 : ℚ) : ℝ) ≤ Real.log (913 : ℕ) / 2 := by
    have h := (log_br_913).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (913 : ℕ) / 2 ≤ ((68167359/20000000 : ℚ) : ℝ) := by
    have h := (log_br_913).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7661163/10000000) (δ := 7139/250000000) 1142 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_914 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (914 : ℕ) / 2)) - ((-4267981/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13635661/4000000 : ℚ) : ℝ) ≤ Real.log (914 : ℕ) / 2 := by
    have h := (log_br_914).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (914 : ℕ) / 2 ≤ ((34089153/10000000 : ℚ) : ℝ) := by
    have h := (log_br_914).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1621029/2500000) (δ := 57103/2000000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_915 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (915 : ℕ) / 2)) - ((-3880009/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1704731/500000 : ℚ) : ℝ) ≤ Real.log (915 : ℕ) / 2 := by
    have h := (log_br_915).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (915 : ℕ) / 2 ≤ ((68189241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_915).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6153931/12500000) (δ := 35711/1250000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_916 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (916 : ℕ) / 2)) - ((111671/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68200163/20000000 : ℚ) : ℝ) ≤ Real.log (916 : ℕ) / 2 := by
    have h := (log_br_916).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (916 : ℕ) / 2 ≤ ((17050041/5000000 : ℚ) : ℝ) := by
    have h := (log_br_916).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6727773/20000000) (δ := 57103/2000000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_917 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (917 : ℕ) / 2)) - ((1875327/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34105537/10000000 : ℚ) : ℝ) ≤ Real.log (917 : ℕ) / 2 := by
    have h := (log_br_917).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (917 : ℕ) / 2 ≤ ((2728443/800000 : ℚ) : ℝ) := by
    have h := (log_br_917).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18063413/100000000) (δ := 35711/1250000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_918 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (918 : ℕ) / 2)) - ((4974919/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68221973/20000000 : ℚ) : ℝ) ≤ Real.log (918 : ℕ) / 2 := by
    have h := (log_br_918).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (918 : ℕ) / 2 ≤ ((34110987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_918).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -250509/10000000) (δ := 57103/2000000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_919 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (919 : ℕ) / 2)) - ((8670723/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68232861/20000000 : ℚ) : ℝ) ≤ Real.log (919 : ℕ) / 2 := by
    have h := (log_br_919).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (919 : ℕ) / 2 ≤ ((34116431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_919).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1303753/10000000) (δ := 57103/2000000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_920 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (920 : ℕ) / 2)) - ((4153547/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8530467/2500000 : ℚ) : ℝ) ≤ Real.log (920 : ℕ) / 2 := by
    have h := (log_br_920).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (920 : ℕ) / 2 ≤ ((68243737/20000000 : ℚ) : ℝ) := by
    have h := (log_br_920).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3570199/12500000) (δ := 35711/1250000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_921 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (921 : ℕ) / 2)) - ((-954121/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((341273/100000 : ℚ) : ℝ) ≤ Real.log (921 : ℕ) / 2 := by
    have h := (log_br_921).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (921 : ℕ) / 2 ≤ ((68254601/20000000 : ℚ) : ℝ) := by
    have h := (log_br_921).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 688593/1562500) (δ := 35711/1250000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_922 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (922 : ℕ) / 2)) - ((-1450849/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17066363/5000000 : ℚ) : ℝ) ≤ Real.log (922 : ℕ) / 2 := by
    have h := (log_br_922).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (922 : ℕ) / 2 ≤ ((68265453/20000000 : ℚ) : ℝ) := by
    have h := (log_br_922).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29780591/50000000) (δ := 35711/1250000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_923 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (923 : ℕ) / 2)) - ((-9901907/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17069073/5000000 : ℚ) : ℝ) ≤ Real.log (923 : ℕ) / 2 := by
    have h := (log_br_923).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (923 : ℕ) / 2 ≤ ((68276293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_923).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37517641/50000000) (δ := 35711/1250000000) 1142 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_924 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (924 : ℕ) / 2)) - ((-8878719/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((853589/250000 : ℚ) : ℝ) ≤ Real.log (924 : ℕ) / 2 := by
    have h := (log_br_924).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (924 : ℕ) / 2 ≤ ((68287121/20000000 : ℚ) : ℝ) := by
    have h := (log_br_924).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3329369/5000000) (δ := 285587/10000000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_925 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (925 : ℕ) / 2)) - ((-4573813/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68297937/20000000 : ℚ) : ℝ) ≤ Real.log (925 : ℕ) / 2 := by
    have h := (log_br_925).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (925 : ℕ) / 2 ≤ ((34148969/10000000 : ℚ) : ℝ) := by
    have h := (log_br_925).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51146113/100000000) (δ := 17851/625000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_926 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (926 : ℕ) / 2)) - ((707207/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34154371/10000000 : ℚ) : ℝ) ≤ Real.log (926 : ℕ) / 2 := by
    have h := (log_br_926).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (926 : ℕ) / 2 ≤ ((68308743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_926).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1428879/4000000) (δ := 285587/10000000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_927 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (927 : ℕ) / 2)) - ((6876139/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13663907/4000000 : ℚ) : ℝ) ≤ Real.log (927 : ℕ) / 2 := by
    have h := (log_br_927).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (927 : ℕ) / 2 ≤ ((4269971/1250000 : ℚ) : ℝ) := by
    have h := (log_br_927).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2539371/12500000) (δ := 17851/625000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_928 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (928 : ℕ) / 2)) - ((4903343/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68330317/20000000 : ℚ) : ℝ) ≤ Real.log (928 : ℕ) / 2 := by
    have h := (log_br_928).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (928 : ℕ) / 2 ≤ ((34165159/10000000 : ℚ) : ℝ) := by
    have h := (log_br_928).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4923663/100000000) (δ := 17851/625000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_929 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (929 : ℕ) / 2)) - ((9138943/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68341087/20000000 : ℚ) : ℝ) ≤ Real.log (929 : ℕ) / 2 := by
    have h := (log_br_929).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (929 : ℕ) / 2 ≤ ((2135659/625000 : ℚ) : ℝ) := by
    have h := (log_br_929).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 653157/6250000) (δ := 17851/625000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_930 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (930 : ℕ) / 2)) - ((5128437/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13670369/4000000 : ℚ) : ℝ) ≤ Real.log (930 : ℕ) / 2 := by
    have h := (log_br_930).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (930 : ℕ) / 2 ≤ ((34175923/10000000 : ℚ) : ℝ) := by
    have h := (log_br_930).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25807557/100000000) (δ := 17851/625000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_931 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (931 : ℕ) / 2)) - ((-750889/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2136331/625000 : ℚ) : ℝ) ≤ Real.log (931 : ℕ) / 2 := by
    have h := (log_br_931).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (931 : ℕ) / 2 ≤ ((68362593/20000000 : ℚ) : ℝ) := by
    have h := (log_br_931).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 411489/1000000) (δ := 285587/10000000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_932 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (932 : ℕ) / 2)) - ((-1270273/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4273333/1250000 : ℚ) : ℝ) ≤ Real.log (932 : ℕ) / 2 := by
    have h := (log_br_932).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (932 : ℕ) / 2 ≤ ((68373329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_932).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2823727/5000000) (δ := 285587/10000000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_933 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (933 : ℕ) / 2)) - ((-9636987/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17096013/5000000 : ℚ) : ℝ) ≤ Real.log (933 : ℕ) / 2 := by
    have h := (log_br_933).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (933 : ℕ) / 2 ≤ ((68384053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_933).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1435661/2000000) (δ := 285587/10000000000) 1142 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_934 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (934 : ℕ) / 2)) - ((-235573/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17098691/5000000 : ℚ) : ℝ) ≤ Real.log (934 : ℕ) / 2 := by
    have h := (log_br_934).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (934 : ℕ) / 2 ≤ ((13678953/4000000 : ℚ) : ℝ) := by
    have h := (log_br_934).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70005203/100000000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_935 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (935 : ℕ) / 2)) - ((-5797197/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13681093/4000000 : ℚ) : ℝ) ≤ Real.log (935 : ℕ) / 2 := by
    have h := (log_br_935).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (935 : ℕ) / 2 ≤ ((34202733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_935).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2189181/4000000) (δ := 285659/10000000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_936 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (936 : ℕ) / 2)) - ((-80427/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34208077/10000000 : ℚ) : ℝ) ≤ Real.log (936 : ℕ) / 2 := by
    have h := (log_br_936).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (936 : ℕ) / 2 ≤ ((13683231/4000000 : ℚ) : ℝ) := by
    have h := (log_br_936).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19735489/50000000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_937 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (937 : ℕ) / 2)) - ((353763/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4276677/1250000 : ℚ) : ℝ) ≤ Real.log (937 : ℕ) / 2 := by
    have h := (log_br_937).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (937 : ℕ) / 2 ≤ ((68426833/20000000 : ℚ) : ℝ) := by
    have h := (log_br_937).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24228133/100000000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_938 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (938 : ℕ) / 2)) - ((9358829/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68437499/20000000 : ℚ) : ℝ) ≤ Real.log (938 : ℕ) / 2 := by
    have h := (log_br_938).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (938 : ℕ) / 2 ≤ ((219/64 : ℚ) : ℝ) := by
    have h := (log_br_938).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -900099/10000000) (δ := 285659/10000000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_939 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (939 : ℕ) / 2)) - ((4846583/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34224077/10000000 : ℚ) : ℝ) ≤ Real.log (939 : ℕ) / 2 := by
    have h := (log_br_939).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (939 : ℕ) / 2 ≤ ((13689631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_939).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3104511/50000000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_940 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (940 : ℕ) / 2)) - ((6553629/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34229399/10000000 : ℚ) : ℝ) ≤ Real.log (940 : ℕ) / 2 := by
    have h := (log_br_940).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (940 : ℕ) / 2 ≤ ((68458799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_940).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5350833/25000000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_941 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (941 : ℕ) / 2)) - ((1073117/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68469431/20000000 : ℚ) : ℝ) ≤ Real.log (941 : ℕ) / 2 := by
    have h := (log_br_941).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (941 : ℕ) / 2 ≤ ((8558679/2500000 : ℚ) : ℝ) := by
    have h := (log_br_941).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1829097/5000000) (δ := 285659/10000000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_942 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (942 : ℕ) / 2)) - ((-4784953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17120013/5000000 : ℚ) : ℝ) ≤ Real.log (942 : ℕ) / 2 := by
    have h := (log_br_942).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (942 : ℕ) / 2 ≤ ((68480053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_942).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51743417/100000000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_943 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (943 : ℕ) / 2)) - ((-1786723/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34245331/10000000 : ℚ) : ℝ) ≤ Real.log (943 : ℕ) / 2 := by
    have h := (log_br_943).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (943 : ℕ) / 2 ≤ ((68490663/20000000 : ℚ) : ℝ) := by
    have h := (log_br_943).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8361149/12500000) (δ := 35693/1250000000) 1142 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_944 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (944 : ℕ) / 2)) - ((-1237913/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68501261/20000000 : ℚ) : ℝ) ≤ Real.log (944 : ℕ) / 2 := by
    have h := (log_br_944).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (944 : ℕ) / 2 ≤ ((34250631/10000000 : ℚ) : ℝ) := by
    have h := (log_br_944).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4691273/6250000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_945 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (945 : ℕ) / 2)) - ((-7359329/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68511849/20000000 : ℚ) : ℝ) ≤ Real.log (945 : ℕ) / 2 := by
    have h := (log_br_945).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (945 : ℕ) / 2 ≤ ((1370237/400000 : ℚ) : ℝ) := by
    have h := (log_br_945).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29972999/50000000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_946 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (946 : ℕ) / 2)) - ((-442613/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2740897/800000 : ℚ) : ℝ) ≤ Real.log (946 : ℕ) / 2 := by
    have h := (log_br_946).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (946 : ℕ) / 2 ≤ ((34261213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_946).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22424379/50000000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_947 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (947 : ℕ) / 2)) - ((3710203/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6853299/2000000 : ℚ) : ℝ) ≤ Real.log (947 : ℕ) / 2 := by
    have h := (log_br_947).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (947 : ℕ) / 2 ≤ ((68532991/20000000 : ℚ) : ℝ) := by
    have h := (log_br_947).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29767221/100000000) (δ := 285673/10000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_948 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (948 : ℕ) / 2)) - ((8320527/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13708709/4000000 : ℚ) : ℝ) ≤ Real.log (948 : ℕ) / 2 := by
    have h := (log_br_948).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (948 : ℕ) / 2 ≤ ((34271773/10000000 : ℚ) : ℝ) := by
    have h := (log_br_948).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7349979/50000000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_949 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (949 : ℕ) / 2)) - ((9999027/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68554087/20000000 : ℚ) : ℝ) ≤ Real.log (949 : ℕ) / 2 := by
    have h := (log_br_949).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (949 : ℕ) / 2 ≤ ((8569261/2500000 : ℚ) : ℝ) := by
    have h := (log_br_949).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 348747/100000000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_950 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (950 : ℕ) / 2)) - ((8165847/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68564619/20000000 : ℚ) : ℝ) ≤ Real.log (950 : ℕ) / 2 := by
    have h := (log_br_950).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (950 : ℕ) / 2 ≤ ((3428231/1000000 : ℚ) : ℝ) := by
    have h := (log_br_950).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15383177/100000000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_951 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (951 : ℕ) / 2)) - ((5427/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3428757/1000000 : ℚ) : ℝ) ≤ Real.log (951 : ℕ) / 2 := by
    have h := (log_br_951).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (951 : ℕ) / 2 ≤ ((68575141/20000000 : ℚ) : ℝ) := by
    have h := (log_br_951).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1900119/6250000) (δ := 285673/10000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_952 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (952 : ℕ) / 2)) - ((-607363/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1371713/400000 : ℚ) : ℝ) ≤ Real.log (952 : ℕ) / 2 := by
    have h := (log_br_952).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (952 : ℕ) / 2 ≤ ((68585651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_952).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45404929/100000000) (δ := 285673/10000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_953 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (953 : ℕ) / 2)) - ((-3739503/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68596149/20000000 : ℚ) : ℝ) ≤ Real.log (953 : ℕ) / 2 := by
    have h := (log_br_953).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (953 : ℕ) / 2 ≤ ((1371923/400000 : ℚ) : ℝ) := by
    have h := (log_br_953).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15098063/25000000) (δ := 28553/1000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_954 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (954 : ℕ) / 2)) - ((-9919343/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17151659/5000000 : ℚ) : ℝ) ≤ Real.log (954 : ℕ) / 2 := by
    have h := (log_br_954).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (954 : ℕ) / 2 ≤ ((68606637/20000000 : ℚ) : ℝ) := by
    have h := (log_br_954).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18840611/25000000) (δ := 285673/10000000000) 1142 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_955 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (955 : ℕ) / 2)) - ((-4455253/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68617113/20000000 : ℚ) : ℝ) ≤ Real.log (955 : ℕ) / 2 := by
    have h := (log_br_955).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (955 : ℕ) / 2 ≤ ((34308557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_955).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66761271/100000000) (δ := 285601/10000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_956 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (956 : ℕ) / 2)) - ((-24061/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68627579/20000000 : ℚ) : ℝ) ≤ Real.log (956 : ℕ) / 2 := by
    have h := (log_br_956).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (956 : ℕ) / 2 ≤ ((3431379/1000000 : ℚ) : ℝ) := by
    have h := (log_br_956).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -202426/390625) (δ := 285601/10000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_957 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (957 : ℕ) / 2)) - ((118419/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68638033/20000000 : ℚ) : ℝ) ≤ Real.log (957 : ℕ) / 2 := by
    have h := (log_br_957).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (957 : ℕ) / 2 ≤ ((34319017/10000000 : ℚ) : ℝ) := by
    have h := (log_br_957).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36897971/100000000) (δ := 285601/10000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_958 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (958 : ℕ) / 2)) - ((1593713/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68648477/20000000 : ℚ) : ℝ) ≤ Real.log (958 : ℕ) / 2 := by
    have h := (log_br_958).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (958 : ℕ) / 2 ≤ ((34324239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_958).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21989161/100000000) (δ := 285601/10000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_959 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (959 : ℕ) / 2)) - ((4799933/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6865891/2000000 : ℚ) : ℝ) ≤ Real.log (959 : ℕ) / 2 := by
    have h := (log_br_959).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (959 : ℕ) / 2 ≤ ((68658911/20000000 : ℚ) : ℝ) := by
    have h := (log_br_959).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7096053/100000000) (δ := 142801/5000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_960 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (960 : ℕ) / 2)) - ((9519503/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17167333/5000000 : ℚ) : ℝ) ≤ Real.log (960 : ℕ) / 2 := by
    have h := (log_br_960).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (960 : ℕ) / 2 ≤ ((68669333/20000000 : ℚ) : ℝ) := by
    have h := (log_br_960).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 972669/12500000) (δ := 142801/5000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_961 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (961 : ℕ) / 2)) - ((246829/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/312500 : ℚ) : ℝ) ≤ Real.log (961 : ℕ) / 2 := by
    have h := (log_br_961).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (961 : ℕ) / 2 ≤ ((13735949/4000000 : ℚ) : ℝ) := by
    have h := (log_br_961).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11322241/50000000) (δ := 142801/5000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_962 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (962 : ℕ) / 2)) - ((71117/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2146567/625000 : ℚ) : ℝ) ≤ Real.log (962 : ℕ) / 2 := by
    have h := (log_br_962).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (962 : ℕ) / 2 ≤ ((13738029/4000000 : ℚ) : ℝ) := by
    have h := (log_br_962).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18745241/50000000) (δ := 142801/5000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_963 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (963 : ℕ) / 2)) - ((-997389/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34350267/10000000 : ℚ) : ℝ) ≤ Real.log (963 : ℕ) / 2 := by
    have h := (log_br_963).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (963 : ℕ) / 2 ≤ ((13740107/4000000 : ℚ) : ℝ) := by
    have h := (log_br_963).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52322207/100000000) (δ := 142801/5000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_964 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (964 : ℕ) / 2)) - ((-112221/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((268402/78125 : ℚ) : ℝ) ≤ Real.log (964 : ℕ) / 2 := by
    have h := (log_br_964).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (964 : ℕ) / 2 ≤ ((68710913/20000000 : ℚ) : ℝ) := by
    have h := (log_br_964).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33568401/50000000) (δ := 142801/5000000000) 1142 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_965 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (965 : ℕ) / 2)) - ((-9907731/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68721281/20000000 : ℚ) : ℝ) ≤ Real.log (965 : ℕ) / 2 := by
    have h := (log_br_965).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (965 : ℕ) / 2 ≤ ((34360641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_965).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75141083/100000000) (δ := 142837/5000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_966 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (966 : ℕ) / 2)) - ((-933687/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34365819/10000000 : ℚ) : ℝ) ≤ Real.log (966 : ℕ) / 2 := by
    have h := (log_br_966).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (966 : ℕ) / 2 ≤ ((68731639/20000000 : ℚ) : ℝ) := by
    have h := (log_br_966).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30178233/50000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_967 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (967 : ℕ) / 2)) - ((-1250123/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2148187/625000 : ℚ) : ℝ) ≤ Real.log (967 : ℕ) / 2 := by
    have h := (log_br_967).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (967 : ℕ) / 2 ≤ ((13748397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_967).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45587551/100000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_968 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (968 : ℕ) / 2)) - ((1655551/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((214851/62500 : ℚ) : ℝ) ≤ Real.log (968 : ℕ) / 2 := by
    have h := (log_br_968).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (968 : ℕ) / 2 ≤ ((68752321/20000000 : ℚ) : ℝ) := by
    have h := (log_br_968).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30832911/100000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_969 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (969 : ℕ) / 2)) - ((1599759/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34381323/10000000 : ℚ) : ℝ) ≤ Real.log (969 : ℕ) / 2 := by
    have h := (log_br_969).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (969 : ℕ) / 2 ≤ ((68762647/20000000 : ℚ) : ℝ) := by
    have h := (log_br_969).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8046273/50000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_970 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (970 : ℕ) / 2)) - ((2496251/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((429831/125000 : ℚ) : ℝ) ≤ Real.log (970 : ℕ) / 2 := by
    have h := (log_br_970).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (970 : ℕ) / 2 ≤ ((68772961/20000000 : ℚ) : ℝ) := by
    have h := (log_br_970).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1369311/100000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_971 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (971 : ℕ) / 2)) - ((8609887/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2149477/625000 : ℚ) : ℝ) ≤ Real.log (971 : ℕ) / 2 := by
    have h := (log_br_971).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (971 : ℕ) / 2 ≤ ((13756653/4000000 : ℚ) : ℝ) := by
    have h := (log_br_971).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13339649/100000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_972 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (972 : ℕ) / 2)) - ((4344459/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34396779/10000000 : ℚ) : ℝ) ≤ Real.log (972 : ℕ) / 2 := by
    have h := (log_br_972).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (972 : ℕ) / 2 ≤ ((68793559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_972).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14017167/50000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_973 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (973 : ℕ) / 2)) - ((-1372447/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53753/15625 : ℚ) : ℝ) ≤ Real.log (973 : ℕ) / 2 := by
    have h := (log_br_973).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (973 : ℕ) / 2 ≤ ((68803841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_973).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42711889/100000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_974 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (974 : ℕ) / 2)) - ((-662587/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68814113/20000000 : ℚ) : ℝ) ≤ Real.log (974 : ℕ) / 2 := by
    have h := (log_br_974).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (974 : ℕ) / 2 ≤ ((34407057/10000000 : ℚ) : ℝ) := by
    have h := (log_br_974).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 57376597/100000000) (δ := 142837/5000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_975 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (975 : ℕ) / 2)) - ((-9662289/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34412187/10000000 : ℚ) : ℝ) ≤ Real.log (975 : ℕ) / 2 := by
    have h := (log_br_975).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (975 : ℕ) / 2 ≤ ((110119/32000 : ℚ) : ℝ) := by
    have h := (log_br_975).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36012087/50000000) (δ := 285529/10000000000) 1142 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_976 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (976 : ℕ) / 2)) - ((-2369361/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((550677/160000 : ℚ) : ℝ) ≤ Real.log (976 : ℕ) / 2 := by
    have h := (log_br_976).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (976 : ℕ) / 2 ≤ ((34417313/10000000 : ℚ) : ℝ) := by
    have h := (log_br_976).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17605539/25000000) (δ := 142773/5000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_977 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (977 : ℕ) / 2)) - ((-6141661/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34422433/10000000 : ℚ) : ℝ) ≤ Real.log (977 : ℕ) / 2 := by
    have h := (log_br_977).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (977 : ℕ) / 2 ≤ ((68844867/20000000 : ℚ) : ℝ) := by
    have h := (log_br_977).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55803129/100000000) (δ := 285657/10000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_978 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (978 : ℕ) / 2)) - ((-96399/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8606887/2500000 : ℚ) : ℝ) ≤ Real.log (978 : ℕ) / 2 := by
    have h := (log_br_978).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (978 : ℕ) / 2 ≤ ((68855097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_978).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10299951/25000000) (δ := 285657/10000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_979 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (979 : ℕ) / 2)) - ((2425013/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17216329/5000000 : ℚ) : ℝ) ≤ Real.log (979 : ℕ) / 2 := by
    have h := (log_br_979).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (979 : ℕ) / 2 ≤ ((68865317/20000000 : ℚ) : ℝ) := by
    have h := (log_br_979).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13305377/50000000) (δ := 285657/10000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_980 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (980 : ℕ) / 2)) - ((886303/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2755021/800000 : ℚ) : ℝ) ≤ Real.log (980 : ℕ) / 2 := by
    have h := (log_br_980).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (980 : ℕ) / 2 ≤ ((34437763/10000000 : ℚ) : ℝ) := by
    have h := (log_br_980).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6018703/50000000) (δ := 142773/5000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_981 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (981 : ℕ) / 2)) - ((9949173/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17221431/5000000 : ℚ) : ℝ) ≤ Real.log (981 : ℕ) / 2 := by
    have h := (log_br_981).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (981 : ℕ) / 2 ≤ ((2755429/800000 : ℚ) : ℝ) := by
    have h := (log_br_981).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1260833/50000000) (δ := 285657/10000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_982 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (982 : ℕ) / 2)) - ((7758983/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68895913/20000000 : ℚ) : ℝ) ≤ Real.log (982 : ℕ) / 2 := by
    have h := (log_br_982).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (982 : ℕ) / 2 ≤ ((34447957/10000000 : ℚ) : ℝ) := by
    have h := (log_br_982).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 533327/3125000) (δ := 142773/5000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_983 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (983 : ℕ) / 2)) - ((604351/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68906091/20000000 : ℚ) : ℝ) ≤ Real.log (983 : ℕ) / 2 := by
    have h := (log_br_983).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (983 : ℕ) / 2 ≤ ((17226523/5000000 : ℚ) : ℝ) := by
    have h := (log_br_983).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31595559/100000000) (δ := 142773/5000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_984 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (984 : ℕ) / 2)) - ((-337703/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34458129/10000000 : ℚ) : ℝ) ≤ Real.log (984 : ℕ) / 2 := by
    have h := (log_br_984).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (984 : ℕ) / 2 ≤ ((68916259/20000000 : ℚ) : ℝ) := by
    have h := (log_br_984).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46108951/100000000) (δ := 285657/10000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_985 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (985 : ℕ) / 2)) - ((-3768203/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4307901/1250000 : ℚ) : ℝ) ≤ Real.log (985 : ℕ) / 2 := by
    have h := (log_br_985).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (985 : ℕ) / 2 ≤ ((68926417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_985).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7576187/12500000) (δ := 285657/10000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_986 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (986 : ℕ) / 2)) - ((-495259/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68936563/20000000 : ℚ) : ℝ) ≤ Real.log (986 : ℕ) / 2 := by
    have h := (log_br_986).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (986 : ℕ) / 2 ≤ ((17234141/5000000 : ℚ) : ℝ) := by
    have h := (log_br_986).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75094339/100000000) (δ := 142773/5000000000) 1142 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_987 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (987 : ℕ) / 2)) - ((-9043237/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((689467/200000 : ℚ) : ℝ) ≤ Real.log (987 : ℕ) / 2 := by
    have h := (log_br_987).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (987 : ℕ) / 2 ≤ ((68946701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_987).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33757363/50000000) (δ := 142809/5000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_988 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (988 : ℕ) / 2)) - ((-524049/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34478413/10000000 : ℚ) : ℝ) ≤ Real.log (988 : ℕ) / 2 := by
    have h := (log_br_988).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (988 : ℕ) / 2 ≤ ((68956827/20000000 : ℚ) : ℝ) := by
    have h := (log_br_988).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53059861/100000000) (δ := 142809/5000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_989 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (989 : ℕ) / 2)) - ((65199/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68966943/20000000 : ℚ) : ℝ) ≤ Real.log (989 : ℕ) / 2 := by
    have h := (log_br_989).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (989 : ℕ) / 2 ≤ ((2155217/625000 : ℚ) : ℝ) := by
    have h := (log_br_989).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9654461/25000000) (δ := 57117/2000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_990 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (990 : ℕ) / 2)) - ((5672273/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68977049/20000000 : ℚ) : ℝ) ≤ Real.log (990 : ℕ) / 2 := by
    have h := (log_br_990).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (990 : ℕ) / 2 ≤ ((1379541/400000 : ℚ) : ℝ) := by
    have h := (log_br_990).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24191529/100000000) (δ := 57117/2000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_991 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (991 : ℕ) / 2)) - ((46223/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13797429/4000000 : ℚ) : ℝ) ≤ Real.log (991 : ℕ) / 2 := by
    have h := (log_br_991).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (991 : ℕ) / 2 ≤ ((34493573/10000000 : ℚ) : ℝ) := by
    have h := (log_br_991).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9779489/100000000) (δ := 57117/2000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_992 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (992 : ℕ) / 2)) - ((9829857/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68997231/20000000 : ℚ) : ℝ) ≤ Real.log (992 : ℕ) / 2 := by
    have h := (log_br_992).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (992 : ℕ) / 2 ≤ ((4312327/1250000 : ℚ) : ℝ) := by
    have h := (log_br_992).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1154569/25000000) (δ := 57117/2000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_993 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (993 : ℕ) / 2)) - ((7248267/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34503653/10000000 : ℚ) : ℝ) ≤ Real.log (993 : ℕ) / 2 := by
    have h := (log_br_993).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (993 : ℕ) / 2 ≤ ((69007307/20000000 : ℚ) : ℝ) := by
    have h := (log_br_993).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19000339/100000000) (δ := 142809/5000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_994 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (994 : ℕ) / 2)) - ((584573/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17254343/5000000 : ℚ) : ℝ) ≤ Real.log (994 : ℕ) / 2 := by
    have h := (log_br_994).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (994 : ℕ) / 2 ≤ ((69017373/20000000 : ℚ) : ℝ) := by
    have h := (log_br_994).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16684777/50000000) (δ := 142809/5000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_995 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (995 : ℕ) / 2)) - ((-3317201/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69027427/20000000 : ℚ) : ℝ) ≤ Real.log (995 : ℕ) / 2 := by
    have h := (log_br_995).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (995 : ℕ) / 2 ≤ ((17256857/5000000 : ℚ) : ℝ) := by
    have h := (log_br_995).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23861533/50000000) (δ := 57117/2000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_996 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (996 : ℕ) / 2)) - ((-3952717/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157421/625000 : ℚ) : ℝ) ≤ Real.log (996 : ℕ) / 2 := by
    have h := (log_br_996).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (996 : ℕ) / 2 ≤ ((69037473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_996).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1939447/3125000) (δ := 142809/5000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_997 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (997 : ℕ) / 2)) - ((-1992591/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69047507/20000000 : ℚ) : ℝ) ≤ Real.log (997 : ℕ) / 2 := by
    have h := (log_br_997).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (997 : ℕ) / 2 ≤ ((17261877/5000000 : ℚ) : ℝ) := by
    have h := (log_br_997).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38193633/50000000) (δ := 57117/2000000000) 1142 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_998 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (998 : ℕ) / 2)) - ((-4420281/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17264383/5000000 : ℚ) : ℝ) ≤ Real.log (998 : ℕ) / 2 := by
    have h := (log_br_998).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (998 : ℕ) / 2 ≤ ((69057533/20000000 : ℚ) : ℝ) := by
    have h := (log_br_998).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66381679/100000000) (δ := 142757/5000000000) 1142 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_999 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (999 : ℕ) / 2)) - ((-1226143/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69067547/20000000 : ℚ) : ℝ) ≤ Real.log (999 : ℕ) / 2 := by
    have h := (log_br_999).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (999 : ℕ) / 2 ≤ ((17266887/5000000 : ℚ) : ℝ) := by
    have h := (log_br_999).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26042633/50000000) (δ := 285689/10000000000) 1142 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1142o2_br_1000 :
    |Real.cos (((1142 : ℕ) : ℝ) * (Real.log (1000 : ℕ) / 2)) - ((4691/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4317347/1250000 : ℚ) : ℝ) ≤ Real.log (1000 : ℕ) / 2 := by
    have h := (log_br_1000).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (1000 : ℕ) / 2 ≤ ((69077553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_1000).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37803129/100000000) (δ := 142757/5000000000) 1142 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos1142o2_br_1000
end AxiomAudit
