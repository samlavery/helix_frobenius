import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table

/-!
# The cosine table at `t = 309/2` (rung-154.5; halved brackets)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos309o2_br_2 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (2 : ℕ) / 2)) - ((961857/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (2 : ℕ) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 692711/10000000) (δ := 7779/1000000000) 309 17
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_3 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (3 : ℕ) / 2)) - ((99599/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (3 : ℕ) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 223973/10000000) (δ := 3929/500000000) 309 27
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_4 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (4 : ℕ) / 2)) - ((425167/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (4 : ℕ) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 692721/5000000) (δ := 987/125000000) 309 34
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_5 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (5 : ℕ) / 2)) - ((-178101/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (5 : ℕ) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6673123/10000000) (δ := 3957/500000000) 309 40
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_6 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (6 : ℕ) / 2)) - ((466761/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (6 : ℕ) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28647/312500) (δ := 7817/1000000000) 309 44
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_7 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (7 : ℕ) / 2)) - ((116373/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (7 : ℕ) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2374441/10000000) (δ := 987/125000000) 309 48
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_8 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (8 : ℕ) / 2)) - ((673939/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (8 : ℕ) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 519543/2500000) (δ := 1547/200000000) 309 51
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_9 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (9 : ℕ) / 2)) - ((983989/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (9 : ℕ) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 223983/5000000) (δ := 7739/1000000000) 309 54
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_10 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (10 : ℕ) / 2)) - ((-183021/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (10 : ℕ) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5980431/10000000) (δ := 3921/500000000) 309 57
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_11 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (11 : ℕ) / 2)) - ((972951/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (11 : ℕ) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -72849/1250000) (δ := 317/40000000) 309 59
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_12 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (12 : ℕ) / 2)) - ((199959/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (12 : ℕ) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 804717/5000000) (δ := 3907/500000000) 309 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_13 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (13 : ℕ) / 2)) - ((903041/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (13 : ℕ) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1110001/10000000) (δ := 247/31250000) 309 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_14 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (14 : ℕ) / 2)) - ((97769/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (14 : ℕ) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1681711/10000000) (δ := 1547/200000000) 309 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_15 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (15 : ℕ) / 2)) - ((-846223/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (15 : ℕ) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -644913/1000000) (δ := 777/100000000) 309 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_16 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (16 : ℕ) / 2)) - ((446129/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (16 : ℕ) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1385451/5000000) (δ := 7913/1000000000) 309 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_17 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (17 : ℕ) / 2)) - ((-248749/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (17 : ℕ) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1307193/2500000) (δ := 3927/500000000) 309 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_18 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (18 : ℕ) / 2)) - ((448849/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (18 : ℕ) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 142587/1250000) (δ := 1973/250000000) 309 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_19 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (19 : ℕ) / 2)) - ((-408353/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (19 : ℕ) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6316189/10000000) (δ := 1557/200000000) 309 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_20 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (20 : ℕ) / 2)) - ((-103561/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (20 : ℕ) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -52877/100000) (δ := 7833/1000000000) 309 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_21 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (21 : ℕ) / 2)) - ((652301/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (21 : ℕ) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2150449/10000000) (δ := 7813/1000000000) 309 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_22 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (22 : ℕ) / 2)) - ((999033/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (22 : ℕ) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54969/5000000) (δ := 7747/1000000000) 309 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_23 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (23 : ℕ) / 2)) - ((101107/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (23 : ℕ) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 785741/5000000) (δ := 7899/1000000000) 309 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_24 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (24 : ℕ) / 2)) - ((605131/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (24 : ℕ) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 460433/2000000) (δ := 3931/500000000) 309 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_25 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (25 : ℕ) / 2)) - ((586003/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (25 : ℕ) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2361699/10000000) (δ := 7769/1000000000) 309 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_26 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (26 : ℕ) / 2)) - ((150217/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (26 : ℕ) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1802731/10000000) (δ := 7727/1000000000) 309 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_27 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (27 : ℕ) / 2)) - ((192819/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log (27 : ℕ) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (27 : ℕ) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 671959/10000000) (δ := 7883/1000000000) 309 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_28 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (28 : ℕ) / 2)) - ((57673/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (28 : ℕ) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -988981/10000000) (δ := 7913/1000000000) 309 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_29 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (29 : ℕ) / 2)) - ((308509/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (29 : ℕ) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3142929/10000000) (δ := 7797/1000000000) 309 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_30 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (30 : ℕ) / 2)) - ((-334097/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (30 : ℕ) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2878219/5000000) (δ := 1551/200000000) 309 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_31 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (31 : ℕ) / 2)) - ((-929357/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log (31 : ℕ) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (31 : ℕ) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6908661/10000000) (δ := 1561/200000000) 309 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_32 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (32 : ℕ) / 2)) - ((46071/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (32 : ℕ) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3463633/10000000) (δ := 3881/500000000) 309 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_33 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (33 : ℕ) / 2)) - ((989719/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (33 : ℕ) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -897/25000) (δ := 973/125000000) 309 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_34 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (34 : ℕ) / 2)) - ((-120609/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (34 : ℕ) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2268021/5000000) (δ := 7777/1000000000) 309 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_35 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (35 : ℕ) / 2)) - ((-444087/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (35 : ℕ) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 333019/500000) (δ := 7727/1000000000) 309 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_36 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (36 : ℕ) / 2)) - ((371461/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (36 : ℕ) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1833427/10000000) (δ := 7783/1000000000) 309 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_37 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (37 : ℕ) / 2)) - ((251401/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (37 : ℕ) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3291673/10000000) (δ := 7863/1000000000) 309 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_38 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (38 : ℕ) / 2)) - ((-235853/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (38 : ℕ) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 175223/250000) (δ := 789/100000000) 309 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_39 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (39 : ℕ) / 2)) - ((860983/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log (39 : ℕ) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (39 : ℕ) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1333993/10000000) (δ := 1561/200000000) 309 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_40 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (40 : ℕ) / 2)) - ((-33003/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (40 : ℕ) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -459497/1000000) (δ := 3899/500000000) 309 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_41 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (41 : ℕ) / 2)) - ((-197571/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (41 : ℕ) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4942547/10000000) (δ := 1551/200000000) 309 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_42 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (42 : ℕ) / 2)) - ((834767/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (42 : ℕ) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -728859/5000000) (δ := 3931/500000000) 309 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_43 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (43 : ℕ) / 2)) - ((-996023/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (43 : ℕ) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7630937/10000000) (δ := 7841/1000000000) 309 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_44 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (44 : ℕ) / 2)) - ((948899/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (44 : ℕ) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 200667/2500000) (δ := 1971/250000000) 309 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_45 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (45 : ℕ) / 2)) - ((-397581/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log (45 : ℕ) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (45 : ℕ) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -778147/1250000) (δ := 7777/1000000000) 309 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_46 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (46 : ℕ) / 2)) - ((617159/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (46 : ℕ) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1132087/5000000) (δ := 7827/1000000000) 309 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_47 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (47 : ℕ) / 2)) - ((-11633/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (47 : ℕ) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5136981/10000000) (δ := 7869/1000000000) 309 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_48 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (48 : ℕ) / 2)) - ((18213/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (48 : ℕ) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 598979/2000000) (δ := 7769/1000000000) 309 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_49 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (49 : ℕ) / 2)) - ((-161437/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (49 : ℕ) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2374451/5000000) (δ := 7791/1000000000) 309 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_50 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (50 : ℕ) / 2)) - ((341981/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (50 : ℕ) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3054429/10000000) (δ := 3931/500000000) 309 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_51 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (51 : ℕ) / 2)) - ((-83577/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (51 : ℕ) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -250239/500000) (δ := 1571/200000000) 309 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_52 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (52 : ℕ) / 2)) - ((541829/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (52 : ℕ) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2495461/10000000) (δ := 1581/200000000) 309 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_53 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (53 : ℕ) / 2)) - ((-348519/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (53 : ℕ) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1171027/2000000) (δ := 3949/500000000) 309 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_54 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (54 : ℕ) / 2)) - ((854673/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (54 : ℕ) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1364689/10000000) (δ := 1937/250000000) 309 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_55 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (55 : ℕ) / 2)) - ((-971523/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (55 : ℕ) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3627967/5000000) (δ := 3931/500000000) 309 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_56 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (56 : ℕ) / 2)) - ((198597/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (56 : ℕ) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -296289/10000000) (δ := 7841/1000000000) 309 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_57 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (57 : ℕ) / 2)) - ((-865063/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (57 : ℕ) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3270091/5000000) (δ := 1953/250000000) 309 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_58 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (58 : ℕ) / 2)) - ((139239/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (58 : ℕ) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2450199/10000000) (δ := 3917/500000000) 309 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_59 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (59 : ℕ) / 2)) - ((-90087/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (59 : ℕ) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4152513/10000000) (δ := 3917/500000000) 309 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_60 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (60 : ℕ) / 2)) - ((-439181/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (60 : ℕ) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1265927/2500000) (δ := 1969/250000000) 309 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_61 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (61 : ℕ) / 2)) - ((215917/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (61 : ℕ) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 660367/5000000) (δ := 3963/500000000) 309 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_62 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (62 : ℕ) / 2)) - ((-994899/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (62 : ℕ) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7601353/10000000) (δ := 7877/1000000000) 309 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_63 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (63 : ℕ) / 2)) - ((143501/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (63 : ℕ) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -240807/1250000) (δ := 973/125000000) 309 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_64 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (64 : ℕ) / 2)) - ((-18321/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (64 : ℕ) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 166253/400000) (δ := 3917/500000000) 309 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_65 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (65 : ℕ) / 2)) - ((-608731/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (65 : ℕ) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5563141/10000000) (δ := 7841/1000000000) 309 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_66 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (66 : ℕ) / 2)) - ((247773/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (66 : ℕ) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 333931/10000000) (δ := 7891/1000000000) 309 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_67 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (67 : ℕ) / 2)) - ((-774631/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (67 : ℕ) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6142319/10000000) (δ := 989/125000000) 309 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_68 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (68 : ℕ) / 2)) - ((16733/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (68 : ℕ) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3843311/10000000) (δ := 3949/500000000) 309 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_69 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (69 : ℕ) / 2)) - ((376499/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (69 : ℕ) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71819/400000) (δ := 1551/200000000) 309 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_70 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (70 : ℕ) / 2)) - ((-979997/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (70 : ℕ) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 735311/1000000) (δ := 1581/200000000) 309 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_71 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (71 : ℕ) / 2)) - ((51013/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (71 : ℕ) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2876051/10000000) (δ := 1551/200000000) 309 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_72 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (72 : ℕ) / 2)) - ((531469/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (72 : ℕ) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2526157/10000000) (δ := 981/125000000) 309 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_73 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (73 : ℕ) / 2)) - ((-1 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (73 : ℕ) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7853819/10000000) (δ := 3949/500000000) 309 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_74 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (74 : ℕ) / 2)) - ((126643/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (74 : ℕ) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2598981/10000000) (δ := 779/100000000) 309 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_75 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (75 : ℕ) / 2)) - ((127787/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (75 : ℕ) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 646423/2500000) (δ := 7913/1000000000) 309 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_76 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (76 : ℕ) / 2)) - ((-15596/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (76 : ℕ) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 154033/200000) (δ := 387/50000000) 309 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_77 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (77 : ℕ) / 2)) - ((75651/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (77 : ℕ) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -591443/2000000) (δ := 7883/1000000000) 309 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_78 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (78 : ℕ) / 2)) - ((688999/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (78 : ℕ) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 506681/2500000) (δ := 787/100000000) 309 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_79 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (79 : ℕ) / 2)) - ((-233733/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (79 : ℕ) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3473581/5000000) (δ := 7883/1000000000) 309 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_80 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (80 : ℕ) / 2)) - ((9901/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (80 : ℕ) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3902239/10000000) (δ := 7877/1000000000) 309 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_81 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (81 : ℕ) / 2)) - ((468233/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (81 : ℕ) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 895951/10000000) (δ := 3913/500000000) 309 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_82 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (82 : ℕ) / 2)) - ((-631367/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (82 : ℕ) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5635277/10000000) (δ := 1969/250000000) 309 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_83 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (83 : ℕ) / 2)) - ((-276317/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (83 : ℕ) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1078159/2000000) (δ := 973/125000000) 309 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_84 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (84 : ℕ) / 2)) - ((190709/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (84 : ℕ) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -765007/10000000) (δ := 7767/500000000) 309 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_85 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (85 : ℕ) / 2)) - ((24179/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (85 : ℕ) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3806049/10000000) (δ := 7769/1000000000) 309 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_86 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (86 : ℕ) / 2)) - ((-491203/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (86 : ℕ) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3692167/5000000) (δ := 7791/1000000000) 309 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_87 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (87 : ℕ) / 2)) - ((6131/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (87 : ℕ) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2918937/10000000) (δ := 989/125000000) 309 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_88 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (88 : ℕ) / 2)) - ((826373/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (88 : ℕ) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1495399/10000000) (δ := 7791/1000000000) 309 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_89 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (89 : ℕ) / 2)) - ((-698383/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (89 : ℕ) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5859831/10000000) (δ := 7841/1000000000) 309 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_90 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (90 : ℕ) / 2)) - ((-18717/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (90 : ℕ) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1106489/2000000) (δ := 3949/500000000) 309 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_91 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (91 : ℕ) / 2)) - ((874799/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (91 : ℕ) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1264441/10000000) (δ := 3101/200000000) 309 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_92 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (92 : ℕ) / 2)) - ((37837/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (92 : ℕ) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 591381/2000000) (δ := 981/125000000) 309 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_93 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (93 : ℕ) / 2)) - ((-479329/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (93 : ℕ) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1426523/2000000) (δ := 3899/500000000) 309 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_94 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (94 : ℕ) / 2)) - ((-102723/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (94 : ℕ) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4444289/10000000) (δ := 7797/1000000000) 309 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_95 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (95 : ℕ) / 2)) - ((15466/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (95 : ℕ) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -356953/10000000) (δ := 7847/1000000000) 309 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_96 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (96 : ℕ) / 2)) - ((19123/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (96 : ℕ) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3687587/10000000) (δ := 1939/250000000) 309 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_97 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (97 : ℕ) / 2)) - ((-199571/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (97 : ℕ) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3845109/5000000) (δ := 7897/1000000000) 309 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_98 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (98 : ℕ) / 2)) - ((-51649/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (98 : ℕ) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1014043/2500000) (δ := 49/6250000) 309 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_99 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (99 : ℕ) / 2)) - ((998547/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (99 : ℕ) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -134807/10000000) (δ := 7813/1000000000) 309 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_100 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (100 : ℕ) / 2)) - ((35943/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (100 : ℕ) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3747121/10000000) (δ := 779/100000000) 309 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_101 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (101 : ℕ) / 2)) - ((-19889/20000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (101 : ℕ) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7590463/10000000) (δ := 779/100000000) 309 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_102 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (102 : ℕ) / 2)) - ((-30683/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (102 : ℕ) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4312049/10000000) (δ := 391/50000000) 309 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_103 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (103 : ℕ) / 2)) - ((976439/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (103 : ℕ) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -135939/2500000) (δ := 7883/1000000000) 309 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_104 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (104 : ℕ) / 2)) - ((72813/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (104 : ℕ) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3188153/10000000) (δ := 7833/1000000000) 309 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_105 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (105 : ℕ) / 2)) - ((-925727/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (105 : ℕ) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6884373/10000000) (δ := 787/100000000) 309 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_106 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (106 : ℕ) / 2)) - ((-474311/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (106 : ℕ) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5162443/10000000) (δ := 3913/500000000) 309 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_107 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (107 : ℕ) / 2)) - ((204301/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log (107 : ℕ) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (107 : ℕ) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1535633/10000000) (δ := 3963/500000000) 309 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_108 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (108 : ℕ) / 2)) - ((42503/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log (108 : ℕ) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (108 : ℕ) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2057419/10000000) (δ := 3963/500000000) 309 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_109 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (109 : ℕ) / 2)) - ((-78223/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (109 : ℕ) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5617331/10000000) (δ := 3913/500000000) 309 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_110 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (110 : ℕ) / 2)) - ((-434823/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (110 : ℕ) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1640801/2500000) (δ := 7769/1000000000) 309 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_111 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (111 : ℕ) / 2)) - ((84249/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (111 : ℕ) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19173/62500) (δ := 3867/500000000) 309 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_112 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (112 : ℕ) / 2)) - ((987453/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (112 : ℕ) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 198221/5000000) (δ := 3917/500000000) 309 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_113 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (113 : ℕ) / 2)) - ((38859/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (113 : ℕ) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1914909/5000000) (δ := 3867/500000000) 309 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_114 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (114 : ℕ) / 2)) - ((-9693/10000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log (114 : ℕ) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (114 : ℕ) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 452057/625000) (δ := 7819/1000000000) 309 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_115 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (115 : ℕ) / 2)) - ((-14149/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (115 : ℕ) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5101659/10000000) (δ := 1973/250000000) 309 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_116 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (116 : ℕ) / 2)) - ((95363/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (116 : ℕ) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1757507/10000000) (δ := 7761/1000000000) 309 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_117 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (117 : ℕ) / 2)) - ((406009/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (117 : ℕ) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 778993/5000000) (δ := 487/62500000) 309 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_118 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (118 : ℕ) / 2)) - ((-179549/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (118 : ℕ) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1211311/2500000) (δ := 3921/500000000) 309 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_119 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (119 : ℕ) / 2)) - ((-497487/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (119 : ℕ) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7603233/10000000) (δ := 7749/1000000000) 309 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_120 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (120 : ℕ) / 2)) - ((-88331/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (120 : ℕ) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4370977/10000000) (δ := 7799/1000000000) 309 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_121 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (121 : ℕ) / 2)) - ((893271/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (121 : ℕ) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -582783/5000000) (δ := 3927/500000000) 309 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_122 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (122 : ℕ) / 2)) - ((692833/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (122 : ℕ) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 402693/2000000) (δ := 7749/1000000000) 309 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_123 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (123 : ℕ) / 2)) - ((-475753/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (123 : ℕ) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 258327/500000) (δ := 7899/1000000000) 309 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_124 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (124 : ℕ) / 2)) - ((-196909/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (124 : ℕ) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -185347/250000) (δ := 3903/500000000) 309 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_125 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (125 : ℕ) / 2)) - ((-6127/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (125 : ℕ) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4311443/10000000) (δ := 7747/1000000000) 309 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_126 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (126 : ℕ) / 2)) - ((176137/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (126 : ℕ) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -616863/5000000) (δ := 7847/1000000000) 309 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_127 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (127 : ℕ) / 2)) - ((46663/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (127 : ℕ) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1819619/10000000) (δ := 7797/1000000000) 309 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_128 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (128 : ℕ) / 2)) - ((-9013/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (128 : ℕ) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 969811/2000000) (δ := 7797/1000000000) 309 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_129 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (129 : ℕ) / 2)) - ((-1 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (129 : ℕ) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7853033/10000000) (δ := 7863/1000000000) 309 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_130 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (130 : ℕ) / 2)) - ((-14739/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (130 : ℕ) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4870411/10000000) (δ := 779/100000000) 309 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_131 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (131 : ℕ) / 2)) - ((45119/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (131 : ℕ) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -238827/1250000) (δ := 49/6250000) 309 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_132 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (132 : ℕ) / 2)) - ((114607/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (132 : ℕ) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1026661/10000000) (δ := 387/50000000) 309 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_133 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (133 : ℕ) / 2)) - ((-591/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (133 : ℕ) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3941767/10000000) (δ := 387/50000000) 309 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_134 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (134 : ℕ) / 2)) - ((-918083/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (134 : ℕ) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6835031/10000000) (δ := 15613/1000000000) 309 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_135 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (135 : ℕ) / 2)) - ((-737713/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (135 : ℕ) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6001183/10000000) (δ := 391/50000000) 309 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_136 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (136 : ℕ) / 2)) - ((305581/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (136 : ℕ) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -157531/500000) (δ := 7883/1000000000) 309 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_137 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (137 : ℕ) / 2)) - ((247943/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (137 : ℕ) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -320913/10000000) (δ := 99/12500000) 309 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_138 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (138 : ℕ) / 2)) - ((544279/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (138 : ℕ) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2488167/10000000) (δ := 777/100000000) 309 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_139 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (139 : ℕ) / 2)) - ((-257071/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (139 : ℕ) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 329813/625000) (δ := 391/50000000) 309 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_140 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (140 : ℕ) / 2)) - ((-997057/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (140 : ℕ) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3831061/5000000) (δ := 7877/1000000000) 309 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_141 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (141 : ℕ) / 2)) - ((-96067/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (141 : ℕ) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4913027/10000000) (δ := 1969/250000000) 309 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_142 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (142 : ℕ) / 2)) - ((642279/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (142 : ℕ) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2183321/10000000) (δ := 1969/250000000) 309 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_143 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (143 : ℕ) / 2)) - ((195569/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (143 : ℕ) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 527227/10000000) (δ := 1969/250000000) 309 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_144 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (144 : ℕ) / 2)) - ((69871/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (144 : ℕ) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3218849/10000000) (δ := 243/31250000) 309 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_145 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (145 : ℕ) / 2)) - ((-44219/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (145 : ℕ) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1472973/2500000) (δ := 3913/500000000) 309 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_146 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (146 : ℕ) / 2)) - ((-961873/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (146 : ℕ) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7161413/10000000) (δ := 1577/200000000) 309 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_147 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (147 : ℕ) / 2)) - ((-118447/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (147 : ℕ) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -452491/1000000) (δ := 3959/500000000) 309 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_148 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (148 : ℕ) / 2)) - ((723111/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (148 : ℕ) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61/320) (δ := 1577/200000000) 309 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_149 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (149 : ℕ) / 2)) - ((961629/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (149 : ℕ) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 173699/2500000) (δ := 1567/200000000) 309 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_150 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (150 : ℕ) / 2)) - ((128271/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (150 : ℕ) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3278383/10000000) (δ := 1967/250000000) 309 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_151 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (151 : ℕ) / 2)) - ((-138817/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (151 : ℕ) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 292243/500000) (δ := 971/125000000) 309 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_152 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (152 : ℕ) / 2)) - ((-122091/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (152 : ℕ) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7313583/10000000) (δ := 7811/1000000000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_153 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (153 : ℕ) / 2)) - ((-167459/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (153 : ℕ) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4780787/10000000) (δ := 3871/500000000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_154 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (154 : ℕ) / 2)) - ((617061/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (154 : ℕ) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -566121/2500000) (δ := 487/62500000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_155 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (155 : ℕ) / 2)) - ((497783/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (155 : ℕ) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 235519/10000000) (δ := 3871/500000000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_156 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (156 : ℕ) / 2)) - ((464451/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (156 : ℕ) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1359727/5000000) (δ := 7761/1000000000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_157 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (157 : ℕ) / 2)) - ((-96623/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (157 : ℕ) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2593757/5000000) (δ := 7861/1000000000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_158 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (158 : ℕ) / 2)) - ((-62271/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (158 : ℕ) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7639893/10000000) (δ := 487/62500000) 309 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_159 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (159 : ℕ) / 2)) - ((-630083/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (159 : ℕ) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2815571/5000000) (δ := 3877/500000000) 309 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_160 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (160 : ℕ) / 2)) - ((283069/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (160 : ℕ) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3209509/10000000) (δ := 3877/500000000) 309 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_161 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (161 : ℕ) / 2)) - ((47443/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (161 : ℕ) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -401489/5000000) (δ := 7849/1000000000) 309 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_162 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (162 : ℕ) / 2)) - ((804791/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (162 : ℕ) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 794341/5000000) (δ := 7849/1000000000) 309 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_163 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (163 : ℕ) / 2)) - ((-15453/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (163 : ℕ) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1982813/5000000) (δ := 7899/1000000000) 309 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_164 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (164 : ℕ) / 2)) - ((-32777/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (164 : ℕ) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 791001/1250000) (δ := 7799/1000000000) 309 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_165 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (165 : ℕ) / 2)) - ((-37857/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (165 : ℕ) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3515971/5000000) (δ := 7847/1000000000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_166 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (166 : ℕ) / 2)) - ((-303577/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (166 : ℕ) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4698103/10000000) (δ := 491/62500000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_167 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (167 : ℕ) / 2)) - ((290313/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (167 : ℕ) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2378247/10000000) (δ := 3903/500000000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_168 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (168 : ℕ) / 2)) - ((499791/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (168 : ℕ) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9037/1250000) (δ := 1939/250000000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_169 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (169 : ℕ) / 2)) - ((630959/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (169 : ℕ) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 111001/500000) (δ := 7897/1000000000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_170 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (170 : ℕ) / 2)) - ((-226727/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log (170 : ℕ) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (170 : ℕ) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 224939/500000) (δ := 3953/500000000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_171 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (171 : ℕ) / 2)) - ((-906481/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (171 : ℕ) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3382087/5000000) (δ := 7897/1000000000) 309 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_172 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (172 : ℕ) / 2)) - ((-223461/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (172 : ℕ) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1672901/2500000) (δ := 49/6250000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_173 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (173 : ℕ) / 2)) - ((-208649/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (173 : ℕ) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2226237/5000000) (δ := 779/100000000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_174 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (174 : ℕ) / 2)) - ((25161/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (174 : ℕ) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -445249/2000000) (δ := 49/6250000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_175 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (175 : ℕ) / 2)) - ((999987/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (175 : ℕ) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6381/5000000) (δ := 779/100000000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_176 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (176 : ℕ) / 2)) - ((128163/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (176 : ℕ) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2188091/10000000) (δ := 7863/1000000000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_177 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (177 : ℕ) / 2)) - ((-178839/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (177 : ℕ) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2188253/5000000) (δ := 7763/1000000000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_178 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (178 : ℕ) / 2)) - ((-867537/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (178 : ℕ) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6552561/10000000) (δ := 779/100000000) 309 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_179 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (179 : ℕ) / 2)) - ((-23527/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (179 : ℕ) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3495757/5000000) (δ := 7833/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_180 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (180 : ℕ) / 2)) - ((-357033/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log (180 : ℕ) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (180 : ℕ) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -967943/2000000) (δ := 7733/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_181 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (181 : ℕ) / 2)) - ((235697/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (181 : ℕ) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2699813/10000000) (δ := 7833/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_182 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (182 : ℕ) / 2)) - ((243491/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (182 : ℕ) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57173/1000000) (δ := 7833/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_183 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (183 : ℕ) / 2)) - ((407551/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (183 : ℕ) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1544727/10000000) (δ := 7783/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_184 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (184 : ℕ) / 2)) - ((22143/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (184 : ℕ) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 729927/2000000) (δ := 7783/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_185 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (185 : ℕ) / 2)) - ((-66423/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (185 : ℕ) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5743149/10000000) (δ := 391/50000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_186 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (186 : ℕ) / 2)) - ((-499967/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (186 : ℕ) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1565069/2000000) (δ := 7833/1000000000) 309 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_187 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (187 : ℕ) / 2)) - ((-68443/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (187 : ℕ) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2905773/5000000) (δ := 317/40000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_188 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (188 : ℕ) / 2)) - ((17529/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (188 : ℕ) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1875779/5000000) (δ := 3939/500000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_189 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (189 : ℕ) / 2)) - ((776953/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (189 : ℕ) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26601/156250) (δ := 317/40000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_190 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (190 : ℕ) / 2)) - ((495497/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log (190 : ℕ) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (190 : ℕ) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 167889/5000000) (δ := 1957/250000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_191 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (191 : ℕ) / 2)) - ((117093/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (191 : ℕ) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1181679/5000000) (δ := 317/40000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_192 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (192 : ℕ) / 2)) - ((-90169/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (192 : ℕ) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4380317/10000000) (δ := 63/8000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_193 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (193 : ℕ) / 2)) - ((-832679/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (193 : ℕ) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6386809/10000000) (δ := 3889/500000000) 309 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_194 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (194 : ℕ) / 2)) - ((-977699/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (194 : ℕ) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3662507/5000000) (δ := 1577/200000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_195 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (195 : ℕ) / 2)) - ((-5353/10000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (195 : ℕ) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5339149/10000000) (δ := 1967/250000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_196 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (196 : ℕ) / 2)) - ((55879/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (196 : ℕ) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3363441/10000000) (δ := 1567/200000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_197 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (197 : ℕ) / 2)) - ((847727/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (197 : ℕ) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -87361/625000) (δ := 1577/200000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_198 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (198 : ℕ) / 2)) - ((975201/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (198 : ℕ) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 557923/10000000) (δ := 3909/500000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_199 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (199 : ℕ) / 2)) - ((67379/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (199 : ℕ) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2503773/10000000) (δ := 3959/500000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_200 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (200 : ℕ) / 2)) - ((-203709/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (200 : ℕ) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1109963/2500000) (δ := 1577/200000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_201 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (201 : ℕ) / 2)) - ((-82811/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (201 : ℕ) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 795789/1250000) (δ := 971/125000000) 309 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_202 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (202 : ℕ) / 2)) - ((-985301/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (202 : ℕ) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -928101/1250000) (δ := 3921/500000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_203 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (203 : ℕ) / 2)) - ((-594111/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (203 : ℕ) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -551739/1000000) (δ := 7761/1000000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_204 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (204 : ℕ) / 2)) - ((122743/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (204 : ℕ) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3619357/10000000) (δ := 1973/250000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_205 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (205 : ℕ) / 2)) - ((38491/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (205 : ℕ) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -346119/2000000) (δ := 7761/1000000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_206 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (206 : ℕ) / 2)) - ((39929/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (206 : ℕ) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5959/400000) (δ := 487/62500000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_207 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (207 : ℕ) / 2)) - ((691111/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (207 : ℕ) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2019429/10000000) (δ := 7761/1000000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_208 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (208 : ℕ) / 2)) - ((9221/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (208 : ℕ) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 970221/2500000) (δ := 3921/500000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_209 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (209 : ℕ) / 2)) - ((-132263/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (209 : ℕ) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 716677/1250000) (δ := 3871/500000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_210 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (210 : ℕ) / 2)) - ((-993873/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (210 : ℕ) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7577103/10000000) (δ := 7761/1000000000) 309 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_211 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (211 : ℕ) / 2)) - ((-162401/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (211 : ℕ) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6295941/10000000) (δ := 3877/500000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_212 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (212 : ℕ) / 2)) - ((-215387/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (212 : ℕ) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -279357/625000) (δ := 7849/1000000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_213 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (213 : ℕ) / 2)) - ((244077/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (213 : ℕ) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1326029/5000000) (δ := 7899/1000000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_214 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (214 : ℕ) / 2)) - ((471849/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (214 : ℕ) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -421451/5000000) (δ := 7749/1000000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_215 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (215 : ℕ) / 2)) - ((57969/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (215 : ℕ) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 191559/2000000) (δ := 247/31250000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_216 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (216 : ℕ) / 2)) - ((453543/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (216 : ℕ) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 55003/200000) (δ := 7749/1000000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_217 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (217 : ℕ) / 2)) - ((-240503/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (217 : ℕ) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22671/50000) (δ := 3877/500000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_218 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (218 : ℕ) / 2)) - ((-815289/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (218 : ℕ) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3155031/5000000) (δ := 7849/1000000000) 309 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_219 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (219 : ℕ) / 2)) - ((-199199/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (219 : ℕ) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7630151/10000000) (δ := 3903/500000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_220 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (220 : ℕ) / 2)) - ((-43839/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (220 : ℕ) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5870473/10000000) (δ := 3953/500000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_221 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (221 : ℕ) / 2)) - ((-76629/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (221 : ℕ) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -128711/312500) (δ := 3953/500000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_222 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (222 : ℕ) / 2)) - ((581687/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (222 : ℕ) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -593747/2500000) (δ := 3903/500000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_223 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (223 : ℕ) / 2)) - ((967509/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (223 : ℕ) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -319513/5000000) (δ := 3903/500000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_224 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (224 : ℕ) / 2)) - ((226647/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (224 : ℕ) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 272293/2500000) (δ := 7797/1000000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_225 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (225 : ℕ) / 2)) - ((432193/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (225 : ℕ) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 702421/2500000) (δ := 7797/1000000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_226 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (226 : ℕ) / 2)) - ((-235969/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (226 : ℕ) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4522529/10000000) (δ := 15497/1000000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_227 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (227 : ℕ) / 2)) - ((-24869/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (227 : ℕ) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3113921/5000000) (δ := 7797/1000000000) 309 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_228 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (228 : ℕ) / 2)) - ((-999589/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (228 : ℕ) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7782321/10000000) (δ := 7889/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_229 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (229 : ℕ) / 2)) - ((-761729/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (229 : ℕ) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -190373/312500) (δ := 1941/250000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_230 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (230 : ℕ) / 2)) - ((-191583/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (230 : ℕ) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4408929/10000000) (δ := 7739/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_231 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (231 : ℕ) / 2)) - ((459567/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (231 : ℕ) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1366611/5000000) (δ := 7739/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_232 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (232 : ℕ) / 2)) - ((910663/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (232 : ℕ) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -133097/1250000) (δ := 3957/500000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_233 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (233 : ℕ) / 2)) - ((242917/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (233 : ℕ) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 596523/10000000) (δ := 7889/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_234 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (234 : ℕ) / 2)) - ((310693/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (234 : ℕ) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 562679/2500000) (δ := 7839/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_235 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (235 : ℕ) / 2)) - ((583/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (235 : ℕ) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3897841/10000000) (δ := 3907/500000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_236 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (236 : ℕ) / 2)) - ((-600713/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (236 : ℕ) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2768987/5000000) (δ := 7789/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_237 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (237 : ℕ) / 2)) - ((-962931/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (237 : ℕ) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1434231/2000000) (δ := 7739/1000000000) 309 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_238 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (238 : ℕ) / 2)) - ((-929629/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (238 : ℕ) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6910503/10000000) (δ := 3941/500000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_239 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (239 : ℕ) / 2)) - ((-518933/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (239 : ℕ) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1058199/2000000) (δ := 1933/250000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_240 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (240 : ℕ) / 2)) - ((99333/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (240 : ℕ) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3678247/10000000) (δ := 979/125000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_241 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (241 : ℕ) / 2)) - ((42231/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (241 : ℕ) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2072219/10000000) (δ := 7821/1000000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_242 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (242 : ℕ) / 2)) - ((982167/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (242 : ℕ) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -94567/2000000) (δ := 7821/1000000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_243 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (243 : ℕ) / 2)) - ((36053/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (243 : ℕ) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 139993/1250000) (δ := 7771/1000000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_244 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (244 : ℕ) / 2)) - ((469141/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (244 : ℕ) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 541239/2000000) (δ := 3941/500000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_245 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (245 : ℕ) / 2)) - ((-71543/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (245 : ℕ) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4285939/10000000) (δ := 15621/1000000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_246 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (246 : ℕ) / 2)) - ((-698223/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (246 : ℕ) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 585927/1000000) (δ := 1933/250000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_247 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (247 : ℕ) / 2)) - ((-985397/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (247 : ℕ) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7426209/10000000) (δ := 1933/250000000) 309 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_248 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (248 : ℕ) / 2)) - ((-22477/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (248 : ℕ) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -134423/200000) (δ := 313/40000000) 309 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_249 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (249 : ℕ) / 2)) - ((-475859/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log (249 : ℕ) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (249 : ℕ) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5166841/10000000) (δ := 3889/500000000) 309 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos309o2_br_250 :
    |Real.cos (((309 : ℕ) : ℝ) * (Real.log (250 : ℕ) / 2)) - ((122999/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (250 : ℕ) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3618713/10000000) (δ := 317/40000000) 309 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos309o2_br_250
end AxiomAudit
